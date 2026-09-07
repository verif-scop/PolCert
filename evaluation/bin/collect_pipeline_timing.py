#!/usr/bin/env python3
"""Measure matched standard-parallel compilation and actual-path stage costs.

Run in an agreed exclusive CPU window. Uses fresh uninstrumented measurements
for both compilers; never imports wall times from another PolOpt version.
"""

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import shlex
import statistics
import tempfile

from collect_monotonic_timing import digest, read_json, run, write_json
from audit_evaluation_timing import distribution

STAGES = ("pluto", "affine_pre_validation", "affine_post_validation",
          "affine_validation", "tiling_validation", "parallel_validation",
          "extraction", "codegen", "others")


def pinned_polycc_text(source, pluto, inscop):
    """Relocate only the two audited executable assignments in upstream polycc.

    POLCERT_PLUTO controls PolCert, not upstream polycc. A hash check of that
    environment variable alone does not bind the baseline producer.
    """
    for name, path in (("pluto", pluto), ("inscop", inscop)):
        source, count = re.subn(r"(?m)^" + name + r"=.*$",
                                lambda _: name + "=" + shlex.quote(str(path)), source)
        if count != 1:
            raise ValueError("Expected one audited polycc assignment: " + name)
    return source


def verify_record(row, fingerprint):
    if row.get("fingerprint") != fingerprint:
        raise ValueError("Cached measurement has a different experiment identity.")
    for stream in ("stdout", "stderr"):
        if digest(Path(row[stream + "_path"])) != row[stream + "_sha256"]:
            raise ValueError("Cached " + stream + " differs from its recorded hash.")
    if row.get("generated_sha256"):
        if digest(Path(row["generated_path"])) != row["generated_sha256"]:
            raise ValueError("Cached baseline C differs from its recorded hash.")
    if "stages_seconds" in row:
        reparsed = parse_actual_profile(Path(row["stderr_path"]).read_text())
        for field in ("stages_seconds", "calls", "total_seconds", "excluded_capture_io_seconds"):
            if reparsed[field] != row[field]:
                raise ValueError("Cached stage values differ from raw stderr: " + field)
        root = Path(row["stderr_path"]).parent.parent
        for relative, expected in row.get("proposal_files", {}).items():
            if digest(root / relative) != expected:
                raise ValueError("Captured proposal differs from its recorded hash: " + relative)


def parse_actual_profile(stderr):
    stages, calls, entries, errors = {}, {}, {}, []
    total, excluded = None, None
    for line in stderr.splitlines():
        if not line.startswith("[pipeline-profile] "):
            continue
        fields = line.split()
        if fields[1] == "region" and len(fields) == 5:
            name = fields[2]
            if name in stages or name not in STAGES:
                errors.append("duplicate or unrecognized stage: " + name)
            calls[name], stages[name] = int(fields[3]), float(fields[4])
        elif fields[1] == "entries" and len(fields) == 4:
            entries[fields[2]] = int(fields[3])
        elif fields[1] == "total" and len(fields) == 3:
            if total is not None:
                errors.append("multiple total markers")
            total = float(fields[2])
        elif fields[1] == "excluded_capture_io" and len(fields) == 3:
            excluded = float(fields[2])
        else:
            errors.append("unrecognized or unfinished profile: " + line)
    if total is None or excluded is None:
        errors.append("missing total/capture boundary")
    if any(not math.isfinite(value) or value < 0 for value in stages.values()):
        errors.append("negative or nonfinite measured interval")
    if total is not None and (not math.isfinite(total) or total < 0):
        errors.append("invalid total")
    if excluded is not None and (not math.isfinite(excluded) or excluded < 0):
        errors.append("invalid capture interval")
    if any(count < 0 for count in (*calls.values(), *entries.values())):
        errors.append("negative invocation count")
    if total is not None and abs(sum(stages.values()) - total) > 1e-6:
        errors.append("stage attribution does not sum to total")
    # Absence is explicitly marked; zeros here mean no invocation in this run,
    # never a fabricated measurement of a parallel-free configuration.
    return {"stages_seconds": {name: stages.get(name, 0.0) for name in STAGES},
            "calls": {name: calls.get(name, 0) for name in STAGES},
            "all_entries": entries, "not_invoked": [name for name in STAGES if name not in stages],
            "total_seconds": total, "excluded_capture_io_seconds": excluded,
            "errors": errors}


def os_release():
    return Path("/etc/os-release").read_text() if Path("/etc/os-release").exists() else None


def route_markers(stderr):
    return [line for line in stderr.splitlines()
            if line.startswith(("[parallel-validation]", "[tiling-validation]", "[alarm]"))]


def summarize(args, cases, fingerprint):
    rows, pending, failed = [], [], []
    for case in cases:
        kernel = case["kernel"]
        paths = [args.output / "wall" / (kernel + "." + compiler + ".repeat-" + str(repeat) + ".json")
                 for repeat in range(1, args.repeats + 1) for compiler in ("pluto", "polcert")]
        phase_path = args.output / "phases" / (kernel + ".json")
        if not all(path.exists() for path in paths) or not phase_path.exists():
            pending.append(kernel)
            continue
        runs = [read_json(path) for path in paths]
        phase = read_json(phase_path)
        try:
            for row in runs + [phase]:
                verify_record(row, fingerprint)
        except (ValueError, KeyError, OSError) as error:
            failed.append({"kernel": kernel, "reason": str(error)})
            continue
        errors = [row for row in runs if not row["valid"]]
        if errors or not phase["valid"]:
            failed.append({"kernel": kernel, "wall_failures": errors, "phase_errors": phase["errors"]})
            continue
        if phase["calls"]["affine_validation"]:
            failed.append({"kernel": kernel, "reason": "Standalone affine call lacks an audited pre/post call-site label."})
            continue
        polcert_outputs = [row["stdout_sha256"] for row in runs if row["compiler"] == "polcert"]
        pluto_outputs = [row["generated_sha256"] for row in runs if row["compiler"] == "pluto"]
        if len(set(polcert_outputs + [phase["stdout_sha256"]])) != 1 or len(set(pluto_outputs)) != 1:
            failed.append({"kernel": kernel, "reason": "output changed between repetitions or profiling"})
            continue
        wall = {compiler + "_wall_seconds": statistics.median(
            row["wall_seconds"] for row in runs if row["compiler"] == compiler)
            for compiler in ("pluto", "polcert")}
        rows.append({"kernel": kernel, **wall,
                     "additional_wall_seconds": wall["polcert_wall_seconds"] - wall["pluto_wall_seconds"],
                     "phase_total_seconds": phase["total_seconds"],
                     "stages_seconds": phase["stages_seconds"], "stage_calls": phase["calls"],
                     "not_invoked": phase["not_invoked"],
                     "polcert_output_sha256": phase["stdout_sha256"],
                     "pluto_output_sha256": pluto_outputs[0],
                     "profile_output_matches_uninstrumented": True,
                     "parallel_output": phase["parallel_output"],
                     "profile_route_markers": phase["route_markers"]})
    result = {"fingerprint": fingerprint, "configuration": "native-default-standard-parallel",
              "requested_kernels": len(cases), "completed_kernels": len(rows),
              "pending": pending, "failed": failed, "per_case": rows,
              "publishable_measurements": len(cases) == len(rows) == 62 and args.repeats == 3 and not failed}
    if rows:
        result["wall_aggregates"] = {name: distribution(row[name] for row in rows)
                                     for name in ("pluto_wall_seconds", "polcert_wall_seconds", "additional_wall_seconds")}
        result["phase_aggregates"] = {name: distribution(row["stages_seconds"][name] for row in rows)
                                      for name in STAGES}
        result["phase_totals"] = {name: sum(row["stages_seconds"][name] for row in rows) for name in STAGES}
        result["stage_invocations"] = {name: sum(row["stage_calls"][name] for row in rows) for name in STAGES}
        result["kernels_with_parallel_validation"] = sum(row["stage_calls"]["parallel_validation"] > 0 for row in rows)
        result["kernels_with_parallel_output"] = sum(row["parallel_output"] for row in rows)
        result["wall_ratio_of_sums"] = sum(row["polcert_wall_seconds"] for row in rows) / sum(row["pluto_wall_seconds"] for row in rows)
        ordered = sorted(rows, key=lambda row: row["additional_wall_seconds"], reverse=True)
        result["largest_cost_cases"] = ordered[:6]
    write_json(args.output / "timing-results.json", result)
    if rows:
        with (args.output / "timing-cases.csv").open("w", newline="") as handle:
            fields = ["kernel", "pluto_wall_seconds", "polcert_wall_seconds", "additional_wall_seconds", "phase_total_seconds", *STAGES]
            writer = csv.DictWriter(handle, fields)
            writer.writeheader()
            for row in rows:
                writer.writerow({**{name: row[name] for name in fields if name in row}, **row["stages_seconds"]})
    print(json.dumps({key: value for key, value in result.items() if key not in ("per_case", "largest_cost_cases")}, indent=2), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profiler-build", type=Path, required=True)
    parser.add_argument("--polopt-sha256", required=True)
    parser.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
    parser.add_argument("--pluto-sha256", required=True)
    parser.add_argument("--polycc", type=Path, default=Path("/pluto/polycc"))
    parser.add_argument("--inscop", type=Path, help="Defaults to the inscop next to --polycc.")
    parser.add_argument("--mode", choices=("all", "wall", "phases", "summarize"), default="all")
    parser.add_argument("--kernel", action="append", help="Smoke-test selection; a partial cohort is never publishable.")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    args.output = args.output.resolve()
    root = args.source_root.resolve()
    args.pluto, args.polycc = args.pluto.resolve(), args.polycc.resolve()
    args.inscop = (args.inscop or args.polycc.parent / "inscop").resolve()
    polopt = root / "polopt"
    manifest, build = read_json(args.manifest), read_json(args.profiler_build / "build-metadata.json")
    flavor = build.get("flavor")
    if flavor not in ("pipeline", "pipeline-vpl"):
        raise SystemExit("Require actual-path pipeline instrumentation.")
    profiler = args.profiler_build.resolve() / ("polopt-profile-" + flavor)
    cohort = [row for row in manifest["cases"] if row["configuration"] == "rectangular"
              and row["source_relative"].startswith("tests/polopt-generated/inputs/")]
    if len(cohort) != 62 or len({row["kernel"] for row in cohort}) != 62:
        raise SystemExit("Frozen core corpus is not the expected 62 distinct kernels.")
    if digest(polopt) != args.polopt_sha256 or digest(args.pluto) != args.pluto_sha256:
        raise SystemExit("Pinned compiler/optimizer hash mismatch.")
    if build["original_polopt_sha256"] != args.polopt_sha256 or build["instrumented_polopt_sha256"] != digest(profiler):
        raise SystemExit("Profiler does not belong to the measured compiler.")
    cases = []
    for old in cohort:
        if args.kernel and old["kernel"] not in args.kernel:
            continue
        case = dict(old)
        case["loop_input"] = str(root / case["source_relative"])
        case["polopt_args"] = ["--parallel"]
        case["pluto_args"] = [arg for arg in case["pluto_args"] if arg != "--noparallel"] + ["--parallel"]
        if any(arg in case["pluto_args"] for arg in ("--rar", "--innerpar", "--noparallel")):
            raise SystemExit("Unexpected baseline setting.")
        case["scalar_no_loop_exception"] = case["kernel"] == "noloop"
        if case["scalar_no_loop_exception"]:
            # Audited scalar assignment input. The requested parallel route
            # rejects before checking on this input; preserve that smoke test.
            case["polopt_args"] = []
            case["pluto_args"] = [arg for arg in case["pluto_args"] if arg != "--parallel"] + ["--noparallel"]
        if digest(Path(case["loop_input"])) != case["source_sha256"]:
            raise SystemExit("Input changed: " + case["kernel"])
        case["c_sha256"] = digest(Path(case["c_source"]))
        cases.append(case)
    if not cases or (args.kernel and set(args.kernel) != {row["kernel"] for row in cases}):
        raise SystemExit("Unknown or empty kernel selection.")
    configuration = root / "tests/pluto/polcert.ini"
    baseline_text = pinned_polycc_text(args.polycc.read_text(), args.pluto, args.inscop)
    baseline = args.output / "baseline-driver" / "polycc"
    identity = {"manifest_sha256": digest(args.manifest), "cases": cases,
                "polopt_sha256": digest(polopt), "profile_polopt_sha256": digest(profiler),
                "pluto_sha256": digest(args.pluto), "polycc_sha256": digest(args.polycc),
                "inscop_sha256": digest(args.inscop),
                "pinned_polycc_sha256": hashlib.sha256(baseline_text.encode()).hexdigest(),
                "config_sha256": digest(configuration), "repeats": args.repeats,
                "collector_sha256": digest(Path(__file__))}
    identity["collector_dependencies_sha256"] = {
        name: digest(Path(__file__).with_name(name))
        for name in ("collect_monotonic_timing.py", "audit_evaluation_timing.py", "collect_vpl_profile.py")}
    fingerprint = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    meta_path = args.output / "run-metadata.json"
    if meta_path.exists() and read_json(meta_path)["fingerprint"] != fingerprint:
        raise SystemExit("Output belongs to a different experiment. Use a fresh directory.")
    baseline.parent.mkdir(parents=True, exist_ok=True)
    if baseline.exists() and baseline.read_text() != baseline_text:
        raise SystemExit("Pinned baseline wrapper changed. Preserve this directory and inspect it.")
    if not baseline.exists():
        baseline.write_text(baseline_text)
        baseline.chmod(0o755)
    protocol = {
        "population": "62 core loop inputs from the frozen retention corpus, with the matching original C inputs for Pluto; four additional retention fixtures are not in this timing cohort.",
        "configuration": "Native PolOpt default affine scheduling, smart fusion, rectangular tiling and standard --parallel; no explicit --innerpar, no RAR, intra-tile rescheduling, diamond, vectorization or unroll-and-jam. Baseline requests the same optimizer settings in one polycc invocation.",
        "wall": "Fresh uninstrumented complete process wall time from Python perf_counter, three repetitions per compiler and kernel. Each repetition alternates Pluto then PolCert on each kernel. Input copying is outside the timer; optimizer subprocesses, parsing and output generation are inside.",
        "stage": "One separately instrumented normal invocation per kernel. CLOCK_MONOTONIC starts at driver initialization and ends at exit; no --profile-stages and no extra diagnostic compilation. Explicit audited call sites distinguish pre-tiling and post-tiling affine validation, including original-proposal checks and retries. Outermost classified regions own nested work: affine checks called by tiling/parallel validation are charged only to that enclosing validator. Any standalone affine call lacking a phase label blocks publication.",
        "baseline_binding": "A private copy of upstream polycc changes only its pluto= and inscop= assignments to the exact recorded absolute executables. The upstream wrapper does not consume POLCERT_PLUTO. Original wrapper, relocated wrapper, Pluto and inscop hashes are all recorded.",
        "vpl_details": flavor == "pipeline-vpl",
        "capture": "The profiled run archives actual scheduler flags, input SCoPs and returned proposals. Measurement-only archive I/O is timed separately and subtracted from stage total. Uninstrumented wall runs invoke pinned Pluto directly, without a recording wrapper.",
        "others": "Residual driver time, including parsing, conversions, normalization, cleanup and printing; extraction is also exported separately for optional grouping. Runtime startup before the driver initialization is outside the stage total but inside process wall time.",
        "not_invoked": "An absent stage is recorded with calls=0 and in not_invoked; aggregate costs include these cases. One scalar assignment input, noloop, has no loop and uses native default [] and baseline --noparallel. Forcing --parallel on it fails in the frozen driver/Pluto path, as preserved by the smoke test; this is not a validator rejection or a measured parallel check. The remaining 61 inputs use the standard-parallel configuration. Missing parallel calls are not silently classified as parallel validation.",
        "output_check": "Require all three uninstrumented PolOpt outputs and the profiled output to match byte-for-byte, and all three baseline generated C outputs to match. This checks instrumentation consistency, not optimization retention or semantic correctness.",
        "aggregation": "Wall: median of three per compiler/kernel, then paired difference and distributions across kernels. Stages: disjoint attribution from one actual invocation per kernel, then distributions across that same cohort. Stage times are not three-run medians.",
    }
    write_json(meta_path, {"fingerprint": fingerprint, **identity, "protocol": protocol,
                          "source_root": str(root), "profiler_build": build,
                          "platform": platform.platform(), "hostname": platform.node(),
                          "container_os_release": os_release()})
    env = os.environ.copy()
    for key in list(env):
        if key.startswith(("POLCERT_DEBUG_", "POLCERT_RETENTION_", "POLCERT_PROFILE_")) or key in ("POLCERT_PARALLEL_DEBUG", "VPLMEASURE_SKIP_DEBUG"):
            del env[key]
    env["COMPCERT_CONFIG"], env["POLCERT_PLUTO"] = str(configuration), str(args.pluto)
    if args.mode in ("all", "wall"):
        for repeat in range(1, args.repeats + 1):
            for index, case in enumerate(cases, 1):
                for compiler in ("pluto", "polcert"):
                    dest = args.output / "wall" / (case["kernel"] + "." + compiler + ".repeat-" + str(repeat))
                    record_path = Path(str(dest) + ".json")
                    if record_path.exists():
                        verify_record(read_json(record_path), fingerprint)
                        continue
                    print("[wall]", index, "/", len(cases), case["kernel"], compiler, repeat, flush=True)
                    if compiler == "pluto":
                        with tempfile.TemporaryDirectory(prefix="polcert-paired-baseline-") as tmp:
                            cwd = Path(tmp)
                            source = Path(case["c_source"])
                            shutil.copy2(source, cwd / source.name)
                            row, stdout, stderr = run([str(baseline), *case["pluto_args"], source.name], cwd, env, dest, args.timeout)
                            generated = cwd / (source.stem + ".pluto.c")
                            row["generated_sha256"] = digest(generated) if generated.exists() else None
                            row["generated_path"] = str(dest) + ".pluto.c"
                            if generated.exists():
                                shutil.copy2(generated, Path(str(dest) + ".pluto.c"))
                            row["valid"] = row["returncode"] == 0 and not row["timed_out"] and generated.exists()
                    else:
                        row, stdout, stderr = run([str(polopt), *case["polopt_args"], case["loop_input"]], root, env, dest, args.timeout)
                        row["valid"] = row["returncode"] == 0 and not row["timed_out"] and "Optimized Loop" in stdout
                    row.update({"kernel": case["kernel"], "compiler": compiler, "repeat": repeat,
                                "stderr_sha256": hashlib.sha256(stderr.encode()).hexdigest(),
                                "fingerprint": fingerprint, "route_markers": route_markers(stderr)})
                    write_json(record_path, row)
    if args.mode in ("all", "phases"):
        for index, case in enumerate(cases, 1):
            dest = args.output / "phases" / case["kernel"]
            record_path = Path(str(dest) + ".json")
            if record_path.exists():
                verify_record(read_json(record_path), fingerprint)
                continue
            print("[phases]", index, "/", len(cases), case["kernel"], flush=True)
            capture = args.output / "proposals" / case["kernel"]
            capture.mkdir(parents=True, exist_ok=False)
            profile_env = {**env, "POLCERT_PROFILE_CAPTURE": str(capture)}
            row, stdout, stderr = run([str(profiler), *case["polopt_args"], case["loop_input"]], root, profile_env, dest, args.timeout)
            parsed = parse_actual_profile(stderr)
            if flavor == "pipeline-vpl":
                from collect_vpl_profile import parse as parse_vpl
                detail = parse_vpl(stderr)
                parsed["vpl_details"] = detail
                parsed["errors"].extend(detail["errors"])
            if row["returncode"] != 0 or row["timed_out"]:
                parsed["errors"].append("instrumented compiler failed")
            row.update({"kernel": case["kernel"], "fingerprint": fingerprint, **parsed,
                        "stderr_sha256": hashlib.sha256(stderr.encode()).hexdigest(),
                        "parallel_output": bool(re.search(r"\bparallel for\b", stdout)),
                        "route_markers": route_markers(stderr),
                        "proposal_files": {str(path.relative_to(args.output)): digest(path) for path in capture.iterdir() if path.is_file()},
                        "valid": not parsed["errors"]})
            write_json(record_path, row)
    for path, expected in ((polopt, identity["polopt_sha256"]),
                           (profiler, identity["profile_polopt_sha256"]),
                           (args.pluto, identity["pluto_sha256"]),
                           (args.inscop, identity["inscop_sha256"]),
                           (baseline, identity["pinned_polycc_sha256"])):
        if digest(path) != expected:
            raise SystemExit("Pinned executable changed during collection: " + str(path))
    result = summarize(args, cases, fingerprint)
    return 1 if result["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
