#!/usr/bin/env python3
"""Measure optimization retention and compilation overhead in a fresh directory."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

from evaluation_io import read_json, sha, write_json


def input_path(package, relative, digest=None):
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError("Input path must stay inside the evaluation package")
    result = (package / path).resolve()
    result.relative_to(package.resolve())
    if not result.is_file() or (digest is not None and sha(result) != digest):
        raise ValueError("Missing or changed packaged input: " + relative)
    return result


def materialize_manifest(package, manifest):
    rows = []
    for old in manifest["cases"]:
        row = dict(old)
        row["loop_input"] = str(input_path(package, row["loop_input"], row["source_sha256"]))
        if row.get("c_source"):
            row["c_source"] = str(input_path(package, row["c_source"], row.get("c_sha256")))
        rows.append(row)
    return {**manifest, "cases": rows}


def select_retention_plan(package, destination, cohorts=None, kernels=None, workers=2):
    plan = read_json(package / "manifests/plan.json")
    available = {c["cohort"] for c in plan["collections"]}
    if cohorts and not set(cohorts) <= available:
        raise ValueError("Unknown retention cohort: " + ", ".join(sorted(set(cohorts) - available)))
    result = {**plan, "collections": [], "native_workers": workers}
    found = set()
    for collection in plan["collections"]:
        if cohorts and collection["cohort"] not in cohorts:
            continue
        source = package / "manifests" / collection["manifest"]
        if sha(source) != collection["manifest_sha256"]:
            raise ValueError("Packaged manifest changed")
        data = materialize_manifest(package, read_json(source))
        if kernels:
            data["cases"] = [r for r in data["cases"] if r["kernel"] in kernels]
        if not data["cases"]:
            continue
        found.update(r["kernel"] for r in data["cases"])
        target = destination / collection["manifest"]
        write_json(target, data)
        result["collections"].append({**collection, "manifest_sha256": sha(target),
                                       "pairs": len(data["cases"]),
                                       "distinct_sources": len({r["source_sha256"] for r in data["cases"]})})
    if not result["collections"] or (kernels and found != set(kernels)):
        raise ValueError("Empty or unknown kernel selection")
    result["planned_pairs"] = sum(c["pairs"] for c in result["collections"])
    result["subset"] = bool(cohorts or kernels)
    write_json(destination / "plan.json", result)
    return destination / "plan.json", result


def execute(command, log):
    log.parent.mkdir(parents=True, exist_ok=True)
    write_json(log.with_suffix(".command.json"), command)
    with log.open("w") as output:
        completed = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT,
                                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    if completed.returncode:
        raise RuntimeError("Command failed (exit " + str(completed.returncode) + "); inspect " + str(log))


def run_retention(args, package):
    args.output.mkdir(parents=True, exist_ok=False)
    plan_file, plan = select_retention_plan(package, args.output / "manifests",
                                           args.cohort, args.kernel, args.workers)
    polopt = args.polopt or args.source / "polopt"
    identity = {"kind": "fresh-retention-collection", "recorded_results_reused": False,
                "compiler_sha256": sha(polopt), "producer_sha256": sha(args.pluto),
                "plan_sha256": sha(plan_file), "subset": plan["subset"],
                "planned_pairs": plan["planned_pairs"], "status": "running",
                "effect_table_status": "not-yet-reviewed"}
    write_json(args.output / "fresh-run.json", identity)
    scripts = package / "bin"
    command = [sys.executable, str(scripts / "run_paired_retention.py"), "--plan", str(plan_file),
               "--source-root", str(args.source), "--polopt", str(polopt), "--pluto", str(args.pluto),
               "--output", str(args.output / "raw")]
    execute(command, args.output / "collection.log")
    identity["status"] = "collected"
    write_json(args.output / "fresh-run.json", identity)
    if not args.no_observe:
        command = [sys.executable, str(scripts / "run_fresh_retention_review.py"), "--plan", str(plan_file),
                   "--raw", str(args.output / "raw"), "--source-root", str(args.source),
                   "--output", str(args.output / "reviews"), "--workers", str(args.observer_workers)]
        execute(command, args.output / "observations.log")
        if any(c["cohort"] == "iss-supplement" for c in plan["collections"]):
            execute([sys.executable, str(scripts / "review_paired_iss.py"), "--raw", str(args.output / "raw"),
                     "--source-root", str(args.source), "--output", str(args.output / "iss-review")],
                    args.output / "iss-observations.log")
        identity["status"] = "collected-and-generically-observed"
        identity["effect_table_status"] = "Inspect observations; unresolved cases require explicit static or source-instance review."
        write_json(args.output / "fresh-run.json", identity)
    print(json.dumps(identity, indent=2))


def run_timing(args, package):
    args.output.mkdir(parents=True, exist_ok=False)
    data = materialize_manifest(package, read_json(package / "manifests/timing.json"))
    write_json(args.output / "manifest.json", data)
    identity = {"kind": "fresh-timing-measurement", "recorded_results_reused": False,
                "compiler_sha256": sha(args.source / "polopt"), "producer_sha256": sha(args.pluto),
                "subset": bool(args.kernel), "repetitions": args.repetitions, "status": "running"}
    write_json(args.output / "fresh-run.json", identity)
    scripts = package / "bin"
    profiler = args.profiler_build or args.output / "profiler"
    if args.profiler_build is None:
        execute([sys.executable, str(scripts / "build_pipeline_profiler.py"), "--source-root", str(args.source),
                 "--assets", str(package / "assets"), "--output", str(profiler)], args.output / "profiler-build.log")
    command = [sys.executable, str(scripts / "collect_pipeline_timing.py"), "--manifest", str(args.output / "manifest.json"),
               "--source-root", str(args.source), "--output", str(args.output / "measurements"),
               "--profiler-build", str(profiler), "--polopt-sha256", identity["compiler_sha256"],
               "--pluto", str(args.pluto), "--pluto-sha256", identity["producer_sha256"],
               "--polycc", str(args.polycc), "--inscop", str(args.inscop), "--repeats", str(args.repetitions),
               "--timeout", str(args.timeout)]
    for kernel in args.kernel or []:
        command += ["--kernel", kernel]
    execute(command, args.output / "timing.log")
    result = read_json(args.output / "measurements/timing-results.json")
    identity["status"] = "measured"
    identity["publishable_measurements"] = result["publishable_measurements"]
    write_json(args.output / "fresh-run.json", identity)
    print(json.dumps(identity, indent=2))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    retention = sub.add_parser("retention", help="Fresh independent baselines, native outputs, and generic effect observations")
    timing = sub.add_parser("timing", help="Fresh complete process timing plus an isolated actual-stage profiler")
    for command in (retention, timing):
        command.add_argument("--source", "--source-root", type=Path, default=Path(__file__).resolve().parents[2], help="Built compiler source tree")
        command.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
        command.add_argument("--output", type=Path, required=True, help="New directory for commands, outputs, and measurements")
        command.add_argument("--kernel", action="append", help="Repeat for a subset; omitted means all selected kernels")
    retention.add_argument("--cohort", action="append", help="Manifest cohort, e.g. standard-parallel or primary-two-level; omitted means all configured pairs")
    retention.add_argument("--polopt", type=Path)
    retention.add_argument("--workers", type=int, choices=(1, 2), default=2)
    retention.add_argument("--observer-workers", type=int, choices=(1, 2), default=2)
    retention.add_argument("--no-observe", action="store_true", help="Collect raw pairs only; do not claim effect retention")
    timing.add_argument("--polycc", type=Path, default=Path("/pluto/polycc"))
    timing.add_argument("--inscop", type=Path, default=Path("/pluto/inscop"))
    timing.add_argument("--profiler-build", type=Path, help="Optional prebuilt matching isolated profiler")
    timing.add_argument("--repetitions", "--repeats", type=int, choices=(3,), default=3)
    timing.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args(argv)
    package = Path(__file__).resolve().parent.parent
    for name in ("source", "pluto", "output", "polopt", "polycc", "inscop", "profiler_build"):
        if getattr(args, name, None) is not None:
            setattr(args, name, getattr(args, name).resolve())
    if args.output.exists():
        raise ValueError("Output already exists; use a fresh directory")
    # Keep generated measurements separate from tracked experiment inputs.
    if args.output == package or package in args.output.parents:
        raise ValueError("Place results outside the evaluation source directory")
    (run_retention if args.command == "retention" else run_timing)(args, package)


if __name__ == "__main__":
    main()
