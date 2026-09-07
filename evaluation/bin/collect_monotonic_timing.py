#!/usr/bin/env python3
"""Collect matched Pluto baseline times and monotonic PolCert phase times.

Reuse the archived, uninstrumented PolCert process measurements, not their
real-time-clock phase profiles or their differently configured Pluto baseline.
Run only in an exclusive measurement window agreed with the retention job.
"""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import statistics
import subprocess
import tempfile
import time

from audit_evaluation_timing import distribution, groups, parse_profile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(path) + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def run(command, cwd, env, destination, timeout):
    started = time.perf_counter()
    proc = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    elapsed = time.perf_counter() - started
    destination.parent.mkdir(parents=True, exist_ok=True)
    Path(str(destination) + ".stdout.txt").write_text(stdout)
    Path(str(destination) + ".stderr.txt").write_text(stderr)
    return {"command": command, "cwd": str(cwd), "wall_seconds": elapsed,
            "returncode": proc.returncode, "timed_out": timed_out,
            "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
            "stdout_path": str(destination) + ".stdout.txt",
            "stderr_path": str(destination) + ".stderr.txt"}, stdout, stderr


def selected_cases(manifest):
    return [row for row in manifest["cases"] if row["configuration"] == "rectangular"
            and row["source_relative"].startswith("tests/polopt-generated/inputs/")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profiler-build", type=Path, required=True)
    parser.add_argument("--polopt", type=Path, default=Path("/tmp/polcert-eval-current/polopt"))
    parser.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
    parser.add_argument("--polycc", type=Path, default=Path("/pluto/polycc"))
    parser.add_argument("--mode", choices=("all", "baseline", "phases", "summarize"), default="all")
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    manifest = read_json(args.manifest)
    cases = selected_cases(manifest)
    if len(cases) != 62 or len({r["kernel"] for r in cases}) != 62:
        raise SystemExit("Expected the same 62 corpus kernels under rectangular tiling.")
    if any("--rar" in row["polopt_args"] or "--rar" in row["pluto_args"] for row in cases):
        raise SystemExit("Archived native PolCert measurements use RAR disabled.")
    source_root = Path(manifest["source_root"])
    archive = read_json(args.archive / "timing-results.json")
    archived_metadata = read_json(args.archive / "run-metadata.json")
    build = read_json(args.profiler_build / "build-metadata.json")
    phase_polopt = args.profiler_build / "polopt-profile-monotonic"
    executables = {"polopt_sha256": digest(args.polopt), "pluto_sha256": digest(args.pluto),
                   "polycc_sha256": digest(args.polycc), "phase_polopt_sha256": digest(phase_polopt)}
    for name in ("polopt_sha256", "pluto_sha256", "polycc_sha256"):
        if executables[name] != archived_metadata["executables"][name]:
            raise SystemExit("Executable differs from archive: " + name)
    if executables["phase_polopt_sha256"] != build["instrumented_polopt_sha256"]:
        raise SystemExit("Profiler differs from its build record.")
    configuration = source_root / "tests/pluto/polcert.ini"
    input_hashes = {}
    for case in cases:
        actual = digest(Path(case["loop_input"]))
        if actual != case["source_sha256"]:
            raise SystemExit("Input differs from retention manifest: " + case["id"])
        input_hashes[case["kernel"]] = {"loop_sha256": actual, "c_sha256": digest(Path(case["c_source"]))}
    identity = {"manifest_sha256": digest(args.manifest), "archive_timing_sha256": digest(args.archive / "timing-results.json"),
                "executables": executables, "config_sha256": digest(configuration), "inputs": input_hashes}
    fingerprint = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    metadata_path = args.output / "run-metadata.json"
    if metadata_path.exists() and read_json(metadata_path)["fingerprint"] != fingerprint:
        raise SystemExit("Output directory belongs to a different measurement identity.")
    metadata = {"fingerprint": fingerprint, **identity, "profiler_build": build,
                "platform": platform.platform(), "host": platform.node(),
                "machine": archived_metadata["machine"],
                "same_container_as_archive": platform.node() == archived_metadata["hostname"],
                "protocol": {
                    "population": "The 62 corpus kernels also included in the retention manifest; one rectangular-tiling configuration per kernel.",
                    "polcert_wall": "Reuse three archived, uninstrumented Python perf_counter process measurements per kernel. Native default: affine scheduling, smart fusion, rectangular tiling; no RAR, intratile rescheduling, diamond tiling, prevectorization, unroll-and-jam, or parallelization.",
                    "pluto_wall": "Three new Python perf_counter measurements of polycc on the matching C source, with the same optimizer settings (including RAR disabled). Temporary input copying is outside the timer. Includes the complete polycc process.",
                    "wall_aggregation": "Per-kernel median of three measurements for each compiler; pair medians on kernel, subtract them, then aggregate over kernels. Baseline and PolCert measurements are separate batches on the same machine, not interleaved repetitions.",
                    "phase_measurement": "One new instrumented invocation per kernel using CLOCK_MONOTONIC. Existing diagnostic mode executes its profiled pipeline then the verified pipeline; retain only the first pipeline's named stage intervals, never the double-compilation process wall time.",
                    "no_loop_input": "The corpus includes one scalar input named noloop. Measure its native default route, which bypasses inapplicable loop optimization; explicitly forcing tiling instead is rejected. Preserve that rejected diagnostic separately.",
                    "phase_aggregation": "Group disjoint stage intervals within the one observed run per kernel, then report their distribution across the 62 kernels. This is not the median-of-three wall-time estimator.",
                    "phase_categories": {"Pluto": "pluto_phase_pipeline: both optimizer invocations (affine scheduling, then identity scheduling with tiling), including writing and reading their SCoP files.", "Validation": "affine_validate + affine_validate_reschedule + checked_tiling_validate", "Verified loop generation": "codegen_elim_schedule + codegen_ast_generate + codegen_polyloop_simpl + codegen_loopgen", "Others": "All remaining named intervals, including extraction, domain strengthening, input/output conversion, normalization, and cleanup. Excludes uninstrumented process startup, parsing, printing, and gaps between named stages."},
                    "archive_input_check": "The old exporter did not record input hashes. Current inputs are checked against the frozen retention manifest; each new profile output must match all three archived uninstrumented outputs. Archive source and binary provenance are retained explicitly.",
                    "invalidated_archive": "Do not reuse old phase times (non-monotonic clock) or the old pure-Pluto baseline (RAR enabled only there).",
                }}
    write_json(metadata_path, metadata)
    write_json(args.output / "selected-manifest.json", {"cases": cases, "source_manifest_sha256": identity["manifest_sha256"]})
    env = os.environ.copy()
    env["COMPCERT_CONFIG"] = str(configuration)
    env["POLCERT_PLUTO"] = str(args.pluto)
    for key in list(env):
        if key.startswith("POLCERT_DEBUG_") or key.startswith("POLCERT_RETENTION_"):
            del env[key]
    if args.mode in ("all", "baseline"):
        for repeat in range(1, 4):
            for index, case in enumerate(cases, 1):
                destination = args.output / "baseline" / (case["id"] + ".repeat-" + str(repeat))
                record = Path(str(destination) + ".json")
                if record.exists():
                    continue
                print("[baseline]", str(index) + "/62", case["kernel"], "repeat", repeat, flush=True)
                with tempfile.TemporaryDirectory(prefix="polcert-baseline-") as tmp:
                    work = Path(tmp)
                    source = Path(case["c_source"])
                    shutil.copy2(source, work / source.name)
                    command = [str(args.polycc), *case["pluto_args"], source.name]
                    row, stdout, stderr = run(command, work, env, destination, args.timeout)
                    row.update({"case": case["kernel"], "repeat": repeat, "generated": (work / (source.stem + ".pluto.c")).exists()})
                    row["valid"] = row["returncode"] == 0 and not row["timed_out"] and row["generated"]
                    write_json(record, row)
    if args.mode in ("all", "phases"):
        for index, case in enumerate(cases, 1):
            destination = args.output / "phases" / case["id"]
            record = Path(str(destination) + ".json")
            if record.exists():
                prior = read_json(record)
                if prior["valid"] or case["kernel"] != "noloop":
                    continue
                for suffix in (".json", ".stdout.txt", ".stderr.txt"):
                    saved = Path(str(destination) + ".explicit-tiling-rejected" + suffix)
                    if saved.exists():
                        raise SystemExit("A rejected no-loop diagnostic already exists; inspect before retrying.")
                    Path(str(destination) + suffix).rename(saved)
            print("[phases]", str(index) + "/62", case["kernel"], flush=True)
            phase_options = [] if case["kernel"] == "noloop" else case["polopt_args"]
            command = [str(phase_polopt), "--profile-stages", *phase_options, case["loop_input"]]
            row, stdout, stderr = run(command, source_root, env, destination, args.timeout)
            stages, errors = parse_profile(stderr)
            metrics = {}
            for line in stderr.splitlines():
                match = re.match(r"^\[profile\]\s+(\S+)\s+(\d+)$", line.strip())
                if match:
                    metrics[match.group(1)] = int(match.group(2))
            if row["returncode"] != 0 or row["timed_out"]:
                errors.append("profile command failed")
            old_output_matches = []
            for repeat in range(1, 4):
                prior = args.archive / "raw/polcert-wall" / (case["kernel"] + ".repeat-" + str(repeat) + ".stdout.txt")
                old_output_matches.append(prior.read_text() == stdout)
            if not all(old_output_matches):
                errors.append("profile output differs from archived native PolCert output")
            row.update({"case": case["kernel"], "repeat": 1, "stages": stages,
                        "structural_metrics": metrics,
                        "groups_seconds": groups(stages), "errors": errors,
                        "archived_output_matches": old_output_matches, "valid": not errors})
            write_json(record, row)
    per_case = []
    failures = []
    pending = []
    for case in cases:
        baseline_files = [args.output / "baseline" / (case["id"] + ".repeat-" + str(r) + ".json") for r in range(1, 4)]
        phase_file = args.output / "phases" / (case["id"] + ".json")
        if not all(p.exists() for p in baseline_files) or not phase_file.exists():
            pending.append(case["kernel"])
            continue
        baseline = [read_json(p) for p in baseline_files]
        phase = read_json(phase_file)
        old = [r for r in archive["runs"] if r["case"] == case["kernel"]]
        if len(old) != 3 or any(r["polcert_wall_status"] != "ok" for r in old):
            failures.append({"case": case["kernel"], "reason": "archived wall repetitions invalid"})
            continue
        if not all(r["valid"] for r in baseline) or not phase["valid"]:
            failures.append({"case": case["kernel"], "baseline_valid": [r["valid"] for r in baseline], "phase_errors": phase["errors"]})
            continue
        pluto_wall = statistics.median(r["wall_seconds"] for r in baseline)
        polcert_wall = statistics.median(r["polcert_wall_seconds"] for r in old)
        per_case.append({"case": case["kernel"], "pluto_wall_seconds": pluto_wall,
                         "polcert_wall_seconds": polcert_wall, "additional_wall_seconds": polcert_wall - pluto_wall,
                         "phase_total_seconds": phase["stages"]["total"],
                         "groups_seconds": phase["groups_seconds"], "stages_seconds": phase["stages"],
                         "structural_metrics": phase["structural_metrics"]})
    result = {"fingerprint": fingerprint, "requested_kernels": len(cases), "completed_kernels": len(per_case),
              "pending_kernels": pending, "failures": failures, "per_case": per_case,
              "publishable_measurements": not pending and not failures and len(per_case) == 62}
    if per_case:
        result["wall_aggregates"] = {key: distribution(row[key] for row in per_case)
                                     for key in ("pluto_wall_seconds", "polcert_wall_seconds", "additional_wall_seconds")}
        result["phase_aggregates"] = {key: distribution(row["groups_seconds"][key] for row in per_case)
                                      for key in ("Pluto", "Validation", "Verified loop generation", "Others")}
        result["wall_ratio_of_sums"] = sum(r["polcert_wall_seconds"] for r in per_case) / sum(r["pluto_wall_seconds"] for r in per_case)
        ordered = sorted(per_case, key=lambda r: r["additional_wall_seconds"], reverse=True)
        result["top_four_additional_time_fraction"] = sum(r["additional_wall_seconds"] for r in ordered[:4]) / sum(r["additional_wall_seconds"] for r in ordered)
        result["largest_cost_cases"] = ordered[:6]
    write_json(args.output / "timing-results.json", result)
    if per_case:
        with (args.output / "timing-cases.csv").open("w", newline="") as handle:
            fields = ["case", "pluto_wall_seconds", "polcert_wall_seconds", "additional_wall_seconds", "phase_total_seconds", "Pluto", "Validation", "Verified loop generation", "Others"]
            writer = csv.DictWriter(handle, fields)
            writer.writeheader()
            for row in per_case:
                writer.writerow({**{key: row[key] for key in fields if key in row}, **row["groups_seconds"]})
    print(json.dumps({key: value for key, value in result.items() if key not in ("per_case", "largest_cost_cases")}, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
