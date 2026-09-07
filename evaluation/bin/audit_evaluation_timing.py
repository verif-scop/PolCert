#!/usr/bin/env python3
"""Diagnose archived real-time-clock phase profiles; not publication data.

Raw logs remain authoritative. Negative durations are errors, not absent stages.
Archived evidence is never edited. Positive intervals do not certify that a
non-monotonic clock did not jump. Use the monotonic collector for final results.
"""

import argparse
import json
import math
from pathlib import Path
import re
import statistics


PROFILE = re.compile(r"^\[profile\]\s+(\S+)\s+(-?\d+(?:\.\d+)?)s$")
VALIDATORS = {"affine_validate", "affine_validate_reschedule", "checked_tiling_validate"}
CODEGEN = {"codegen_elim_schedule", "codegen_ast_generate", "codegen_polyloop_simpl", "codegen_loopgen"}


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def parse_profile(text):
    stages = {}
    errors = []
    for line in text.splitlines():
        match = PROFILE.match(line.strip())
        if not match:
            continue
        name, raw = match.groups()
        if name in stages:
            errors.append("duplicate stage: " + name)
        value = float(raw)
        stages[name] = value
        if value < 0:
            errors.append("negative duration: " + name)
    if "total" not in stages:
        errors.append("missing total")
    else:
        residual = stages["total"] - sum(v for k, v in stages.items() if k != "total")
        if abs(residual) > max(len(stages), 1) * 0.000001:
            errors.append("stage sum differs from total")
    for required in ("extract", "codegen_ast_generate", "codegen_polyloop_simpl", "codegen_loopgen"):
        if required not in stages:
            errors.append("missing stage: " + required)
    return stages, errors


def groups(stages):
    values = {
        "Pluto": stages.get("pluto_phase_pipeline", 0.0),
        "Validation": sum(stages.get(k, 0.0) for k in VALIDATORS),
        "Verified loop generation": sum(stages.get(k, 0.0) for k in CODEGEN),
        "Others": sum(v for k, v in stages.items() if k not in VALIDATORS | CODEGEN | {"total", "pluto_phase_pipeline"}),
    }
    return values


def distribution(values):
    values = sorted(values)
    position = (len(values) - 1) * 0.95
    lo, hi = math.floor(position), math.ceil(position)
    return {"count": len(values), "sum_seconds": sum(values), "mean_seconds": statistics.mean(values),
            "median_seconds": statistics.median(values), "p95_seconds": values[lo] + (position - lo) * (values[hi] - values[lo]),
            "max_seconds": values[-1]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repair", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.repair:
        raise SystemExit("Real-time-clock repairs are disabled: use the isolated monotonic profiler and recollect phase data.")
    archived = read_json(args.input / "timing-results.json")
    metadata = read_json(args.input / "run-metadata.json")
    invalid = []
    valid = []
    for old in archived["runs"]:
        raw = args.input / "raw/timing" / (old["case"] + ".repeat-" + str(old["repeat"]) + ".stderr.txt")
        stages, errors = parse_profile(raw.read_text())
        row = {"case": old["case"], "repeat": old["repeat"], "stages": stages,
               "errors": errors, "stderr_path": str(raw)}
        if errors:
            invalid.append(dict(row))
        if not row["errors"]:
            valid.append(row)
    per_case = []
    for case in sorted({row["case"] for row in archived["runs"]}):
        rows = sorted((r for r in valid if r["case"] == case), key=lambda r: r["stages"]["total"])
        if not rows:
            continue
        # Select the middle total-duration run, or average the two middle runs.
        # All categories consequently add up to the reported median total.
        middle = rows[(len(rows) - 1) // 2:len(rows) // 2 + 1]
        selected_groups = [groups(row["stages"]) for row in middle]
        per_case.append({"case": case, "valid_repeats": len(rows),
                         "selected_repeats": [r["repeat"] for r in middle],
                         "total_seconds": statistics.mean(r["stages"]["total"] for r in middle),
                         "groups_seconds": {key: statistics.mean(g[key] for g in selected_groups) for key in selected_groups[0]}})
    grouped = {key: distribution(row["groups_seconds"][key] for row in per_case)
               for key in ("Pluto", "Validation", "Verified loop generation", "Others")}
    result = {"archived_input": str(args.input), "executables": metadata["executables"],
              "publication_status": "archived_clock_not_suitable_for_publication",
              "warning": "Even positive stage durations can be distorted by wall-clock jumps. Grouped values below are diagnostic only. Stage total is defined as the sum, so agreement is not an independent timing check.",
              "method": {"phase_estimator": "Categories measured in the median-total repetition for each kernel; with an even valid count, average both middle repetitions.",
                         "scope": "Default affine-scheduling and rectangular-tiling configuration; phase profiler does not support ISS, second-level tiling, or parallelization.",
                         "timer": "Existing Unix.gettimeofday phase timers; report negative durations and stage-accounting errors. All archived phase times remain unsuitable for publication, including positive durations.",
                         "wall_time": "Archived Python perf_counter measurements are independent, uninstrumented process runs; phase totals are not full-process wall times."},
              "invalid_archived_profiles": invalid, "valid_profile_count": len(valid),
              "requested_profile_count": len(archived["runs"]), "per_case": per_case,
              "grouped_phase_times": grouped, "archived_wall_aggregates": {k: v for k, v in archived["aggregate"].items() if "wall" in k},
              "all_profiles_valid_after_repairs": False,
              "syntactically_valid_profile_count": len(valid)}
    write_json(args.output / "timing-audit.json", result)
    print(json.dumps({"publication_status": result["publication_status"], "warning": result["warning"],
                      "invalid_archived": [(r["case"], r["repeat"], r["errors"]) for r in invalid],
                      "valid_profiles": len(valid), "requested_profiles": len(archived["runs"]),
                      "grouped_phase_times": grouped}, indent=2))


if __name__ == "__main__":
    main()
