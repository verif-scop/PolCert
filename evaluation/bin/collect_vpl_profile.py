#!/usr/bin/env python3
"""Collect nested VPL timings from a frozen rectangular-tiling cohort.

These diagnostic data explain operation costs; they do not replace the
uninstrumented three-repeat compilation-time experiment.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def parse(stderr):
    stages = {}
    regions = []
    metrics = {}
    errors = []
    for line in stderr.splitlines():
        match = re.fullmatch(r"\[vpl-profile\] region (\S+) (\d+) ([\d.-]+) ([\d.-]+)", line)
        if match:
            key, calls, inclusive, exclusive = match.groups()
            stage, path = key.split("|", 1)
            row = {"stage": stage, "path": path, "operation": path.rsplit("/", 1)[-1],
                   "calls": int(calls), "inclusive_seconds": float(inclusive), "exclusive_seconds": float(exclusive)}
            if row["inclusive_seconds"] < 0 or row["exclusive_seconds"] < -1e-8:
                errors.append("negative monotonic interval: " + key)
            regions.append(row)
        match = re.fullmatch(r"\[vpl-profile\] metric (\S+) (\d+)", line)
        if match:
            key, value = match.groups()
            metrics[key] = int(value)
        match = re.fullmatch(r"\[profile\]\s+(\S+)\s+([\d.-]+)s", line)
        if match:
            stages[match.group(1)] = float(match.group(2))
    grouped = defaultdict(lambda: defaultdict(float))
    operations = defaultdict(lambda: defaultdict(lambda: {"calls": 0, "inclusive_seconds": 0.0, "exclusive_seconds": 0.0}))
    for row in regions:
        op = row["operation"]
        if op.startswith("simplex_"):
            category = "simplex"
        elif op == "debug_formatting":
            category = "discarded_debug_formatting"
        elif op.startswith("core_"):
            category = "polyhedral_core_other"
        elif op.startswith("oracle_"):
            category = "oracle_interface"
        elif op in ("canonize", "isBottom", "integer_tightening", "constraint_insertion", "constraint_certificate_check", "vpl_conversion_in", "vpl_conversion_out"):
            category = "verified_polyhedral_frontend"
        elif op in ("statement_pair", "statement_pair_integer", "access_pair", "access_pair_integer", "dependence_query", "dependence_query_integer", "band_guard_construction"):
            category = "query_preparation"
        elif op == "stage_other":
            category = "other_checks"
        else:
            raise ValueError("Unclassified operation: " + op)
        grouped[row["stage"]][category] += row["exclusive_seconds"]
        aggregate = operations[row["stage"]][op]
        for key in ("calls", "inclusive_seconds", "exclusive_seconds"):
            aggregate[key] += row[key]
    for stage, categories in grouped.items():
        roots = [row for row in regions if row["stage"] == stage and row["path"] == "stage_other"]
        if len(roots) != 1:
            errors.append("expected one stage root: " + stage)
        elif abs(sum(categories.values()) - roots[0]["inclusive_seconds"]) > 1e-5:
            errors.append("exclusive accounting mismatch: " + stage)
    if not regions:
        errors.append("no instrumented regions")
    return {"stages_seconds": stages, "regions": regions, "metrics": metrics,
            "exclusive_categories_seconds": grouped, "operations": operations, "errors": errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--reference-phases", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--kernels", help="Comma-separated subset; omitted means all 62 core kernels.")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--skip-debug-formatting", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    build = json.loads((args.build / "build-metadata.json").read_text())
    root = Path(manifest["source_root"])
    binary = args.build / "polopt-profile-vpl"
    pluto = Path("/pluto/tool/pluto")
    cases = [row for row in manifest["cases"] if row["configuration"] == "rectangular"
             and row["source_relative"].startswith("tests/polopt-generated/inputs/")]
    if len(cases) != 62:
        raise SystemExit("Expected the frozen 62-kernel primary timing cohort.")
    if args.kernels:
        names = args.kernels.split(",")
        lookup = {row["kernel"]: row for row in cases}
        cases = [lookup[name] for name in names]
    if digest(binary) != build["instrumented_polopt_sha256"]:
        raise SystemExit("Instrumented executable hash mismatch.")
    if digest(root / "polopt") != build["original_polopt_sha256"]:
        raise SystemExit("Frozen executable hash mismatch.")
    metadata = {"manifest_sha256": digest(args.manifest), "build_metadata_sha256": digest(args.build / "build-metadata.json"),
                "original_polopt_sha256": build["original_polopt_sha256"], "instrumented_polopt_sha256": digest(binary),
                "pluto_sha256": digest(pluto), "config_sha256": digest(root / "tests/pluto/polcert.ini"),
                "clock": "CLOCK_MONOTONIC", "repeats": 1,
                "skip_debug_formatting": args.skip_debug_formatting,
                "protocol": "One diagnostic stage-profile invocation per frozen 62-kernel rectangular configuration. The existing diagnostic command compiles twice; instrumentation is active only inside named stages of the first profiled pipeline. Generated stdout must match the previous monotonic phase archive byte-for-byte. Exclusive time subtracts immediate nested children; inclusive columns must never be summed across nested operations. Original wall-time data remain unchanged.",
                "limitations": "Timers, stack/path bookkeeping, and structural counters add overhead. Use these data for cost attribution, not as replacement uninstrumented compilation times. Query preparation is the exclusive time in statement/access/query/guard construction scopes; non-query validation checks remain separate."}
    existing = args.output / "run-metadata.json"
    if existing.exists() and json.loads(existing.read_text()) != metadata:
        raise SystemExit("Output directory has a different experiment identity.")
    save(existing, metadata)
    environment = os.environ.copy()
    for key in list(environment):
        if key.startswith("POLCERT_"):
            del environment[key]
    environment["POLCERT_PLUTO"] = str(pluto)
    environment["VPLMEASURE_SKIP_DEBUG"] = "1" if args.skip_debug_formatting else "0"
    environment["COMPCERT_CONFIG"] = str(root / "tests/pluto/polcert.ini")
    for index, case in enumerate(cases, 1):
        record = args.output / "cases" / (case["kernel"] + ".json")
        if record.exists():
            continue
        if digest(Path(case["loop_input"])) != case["source_sha256"]:
            raise SystemExit("Frozen source hash mismatch: " + case["id"])
        print("[vpl-profile]", index, "/", len(cases), case["kernel"], flush=True)
        flags = [] if case["kernel"] == "noloop" else case["polopt_args"]
        command = [str(binary), "--profile-stages", *flags, case["loop_input"]]
        started = time.perf_counter()
        process = subprocess.Popen(command, cwd=root, env=environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        elapsed = time.perf_counter() - started
        record.parent.mkdir(parents=True, exist_ok=True)
        record.with_suffix(".stdout.txt").write_text(stdout)
        record.with_suffix(".stderr.txt").write_text(stderr)
        row = parse(stderr)
        reference = args.reference_phases / (case["id"] + ".stdout.txt")
        matches = reference.read_text() == stdout
        if not matches:
            row["errors"].append("output differs from frozen monotonic phase archive")
        if process.returncode or timed_out:
            row["errors"].append("compiler invocation failed or timed out")
        row.update({"case": case["kernel"], "id": case["id"], "command": command,
                    "input_sha256": case["source_sha256"], "returncode": process.returncode,
                    "timed_out": timed_out, "diagnostic_process_seconds": elapsed,
                    "stdout_sha256": digest(record.with_suffix(".stdout.txt")),
                    "reference_stdout_sha256": digest(reference), "reference_output_equal": matches,
                    "valid": not row["errors"]})
        save(record, row)
        print("[done]", case["kernel"], round(elapsed, 3), "s", "valid=" + str(row["valid"]), flush=True)
        if row["errors"]:
            print(json.dumps(row["errors"]), flush=True)
    rows = [json.loads(path.read_text()) for path in sorted((args.output / "cases").glob("*.json"))]
    save(args.output / "profile-results.json", {"completed": len(rows), "valid": sum(row["valid"] for row in rows), "per_case": rows})


if __name__ == "__main__":
    main()
