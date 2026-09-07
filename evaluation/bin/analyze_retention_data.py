#!/usr/bin/env python3
"""Derive effect-level evidence from independently captured paired outputs."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

from retention_scop import analyze_producer
from retention_trace import compare_case
from retention_identity import audit_scop


TARGETS = {
    "affine": "affine", "iss": "iss", "rectangular": "rectangular_tiling",
    "two-level": "two_level_tiling", "diamond": "diamond_tiling",
    "parallel": "parallelization",
}
ANALYSIS_HASH = hashlib.sha256(b"".join(
    (Path(__file__).parent / name).read_bytes()
    for name in ["analyze_retention_data.py", "retention_scop.py", "retention_trace.py", "retention_candidate.py", "retention_baseline.py", "retention_identity.py"]
)).hexdigest()


def dump(path, value):
    temporary = path.with_suffix(".pending.json")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def analyze_case(case, source_root, reuse_traces_from=None):
    if reuse_traces_from is not None:
        raise ValueError("Legacy trace reuse is disabled; rerun traces without --reuse-traces-from")
    raw = json.loads((case / "result.json").read_text())
    producer = analyze_producer(case)
    geometry = producer.get("final_geometry") or {}
    identity = (audit_scop(Path(producer['producer_c_file']).parent / 'input.scop')
                if producer.get('producer_c_file') else {'identity_safe': False, 'status': 'no-paired-source'})
    tile_rows = geometry.get("tile_schedule_rows", [])
    kept = geometry.get("canonical_kept_schedule_rows", [])
    try:
        trace = compare_case(case, source_root, tile_rows, kept, geometry,
                             producer.get("producer_c_file"), producer.get("producer_c_sha256"))
    except Exception as error:
        trace = {"status": "analysis-error", "detail": type(error).__name__ + ": " + str(error)}
    dump(case / "trace-comparison.json", trace)
    effects = {}
    outer_level_indices = set()
    for statement in geometry.get("statements", []):
        active = [coordinate for coordinate in statement["coordinates"]
                  if coordinate["varies"] is True and coordinate["scheduled"]]
        outer_level_indices.update(index for index, coordinate in enumerate(active)
                                   if coordinate["level"] is not None and coordinate["level"] >= 2)
    for family, entry in producer["effects"].items():
        produced = entry["status"]
        if family == "parallelization" and trace.get("status") == "compared":
            witnesses = [row for row in trace["observations"]
                         if row["pluto"]["status"] == "ok" and row["pluto"]["statements"] > 0]
            if any(row["pluto"]["parallel_loops"] > 0 for row in witnesses):
                produced = "observed"
        retained = "not-applicable" if produced == "absent" else "unresolved"
        if produced == "observed":
            if raw["timed_out"]:
                retained = "timeout"
            elif raw["returncode"] != 0:
                retained = "rejected"
            elif trace.get("access_match"):
                if family == "affine":
                    retained = "sampled-retained"
                elif family in {"rectangular_tiling", "two_level_tiling", "diamond_tiling"}:
                    if trace.get("shape_match") and trace.get("varying_tile_coordinates"):
                        if family != "two_level_tiling" or outer_level_indices.intersection(trace["varying_tile_coordinates"]):
                            retained = "sampled-retained"
                elif family == "parallelization":
                    # Loop counts cannot establish which source iterations
                    # execute together. The fresh membership reviewer supplies
                    # the effect judgment; this preliminary trace does not.
                    retained = "requires-parallel-membership-comparison"
                elif family == "iss":
                    # Preserving an execution trace alone does not establish
                    # that the domain split remains in the final loop.
                    retained = "unresolved-partition-structure"
        if retained == 'sampled-retained' and not identity['identity_safe']:
            retained = 'requires-source-instance-review'
        effects[family] = {"producer": produced, "retention": retained}
    stderr = (case / "polcert.stderr.txt").read_text()
    failure = None
    if raw["timed_out"]:
        failure = "compilation-timeout"
    elif raw["returncode"]:
        if "Post-tiling affine validation failed" in stderr:
            failure = "post-tiling-affine-rejection"
        elif "Tiling validation rejected or unavailable" in stderr:
            failure = "tiling-stage-rejected-or-unavailable"
        elif "Affine validation" in stderr:
            failure = "affine-stage-rejection"
        else:
            failure = "compilation-failure"
    return {"analysis_sha256": ANALYSIS_HASH, "reused_trace_from_analysis_sha256": reuse_traces_from,
            "id": raw["id"], "kernel": raw["kernel"], "source_sha256": raw['source_sha256'],
            "identity_audit": identity,
            "configuration": raw["configuration"], "returncode": raw["returncode"],
            "timed_out": raw["timed_out"], "failure_class": failure,
            "effects": effects, "producer_analysis": producer, "trace_analysis": trace}


def summarize(root):
    manifest = json.loads((root / "manifest.json").read_text())
    rows = [json.loads(path.read_text()) for path in (root / "cases").glob("*/effect-analysis.json")]
    rows = [row for row in rows if row.get("analysis_sha256") == ANALYSIS_HASH]
    completed = list((root / "cases").glob("*/result.json"))
    primary = []
    for configuration, family in TARGETS.items():
        subset = [row for row in rows if row["configuration"] == configuration]
        counts = Counter((row["effects"][family]["producer"], row["effects"][family]["retention"])
                         for row in subset)
        primary.append({
            "configuration": configuration, "target_effect": family,
            "planned_pairs": sum(row["configuration"] == configuration for row in manifest["cases"]),
            "analyzed_pairs": len(subset),
            "producer_observed": sum(value for (status, _), value in counts.items() if status == "observed"),
            "sampled_retained": counts[("observed", "sampled-retained")],
            "rejected": counts[("observed", "rejected")],
            "timeout": counts[("observed", "timeout")],
            "unresolved": sum(value for (status, retention), value in counts.items()
                              if status == "observed" and retention.startswith("unresolved")),
            "producer_absent": sum(value for (status, _), value in counts.items() if status == "absent"),
            "producer_unknown": sum(value for (status, _), value in counts.items() if status == "unknown"),
        })
    all_effects = {}
    for family in TARGETS.values():
        all_effects[family] = dict(Counter(
            row["effects"][family]["producer"] + ":" + row["effects"][family]["retention"] for row in rows))
    combinations = [row for row in rows if row["configuration"] not in TARGETS]
    summary = {
        "analysis_sha256": ANALYSIS_HASH,
        "complete_collection": len(completed) == len(manifest["cases"]),
        "complete_analysis": len(rows) == len(manifest["cases"]),
        "planned_pairs": len(manifest["cases"]), "completed_pairs": len(completed), "analyzed_pairs": len(rows),
        "primary_configuration_target_effect": primary, "all_observed_effects": all_effects,
        "selected_combinations": [{"id": row["id"], "effects": row["effects"], "failure_class": row["failure_class"]} for row in combinations],
        "failures": [{"id": row["id"], "failure_class": row["failure_class"]} for row in rows if row["failure_class"]],
        "method": {
            "producer": "The explicitly paired independent Pluto baseline; requested flags do not establish effects.",
            "retained": "Complete nonempty bounded samples agree in instruction-access order; tiling additionally agrees in actual tile-coordinate grouping and crosses at least one tile boundary.",
            "limitations": "Sampled retention is not an all-input structural equivalence proof. Unresolved comparisons and partial samples remain explicit. A rejection need not mean that the producer's transformation was legal.",
        },
    }
    dump(root / "retention-summary.json", summary)
    dump(root / "retention-rows.json", rows)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--case", type=Path)
    parser.add_argument("--follow", action="store_true")
    parser.add_argument("--reuse-traces-from", help="Disabled legacy option; traces must be rerun")
    args = parser.parse_args()
    if args.reuse_traces_from is not None:
        parser.error("Legacy trace reuse is disabled; rerun traces without --reuse-traces-from")
    if args.case:
        dump(args.case / "effect-analysis.json", analyze_case(args.case, args.source_root, args.reuse_traces_from))
        return
    while True:
        for path in sorted((args.root / "cases").glob("*/result.json")):
            target = path.parent / "effect-analysis.json"
            if target.exists() and json.loads(target.read_text()).get("analysis_sha256") == ANALYSIS_HASH:
                continue
            try:
                command = [sys.executable, str(Path(__file__).absolute()), str(args.root),
                           "--source-root", str(args.source_root), "--case", str(path.parent)]
                result = subprocess.run(command,
                                        capture_output=True, text=True, timeout=60)
                if result.returncode:
                    print("analysis failed " + path.parent.name + ": " + result.stderr[-500:], flush=True)
            except subprocess.TimeoutExpired:
                print("analysis timeout " + path.parent.name, flush=True)
            current = summarize(args.root)
            print("analyzed {}/{} collected {}: {}".format(current["analyzed_pairs"], current["planned_pairs"], current["completed_pairs"], path.parent.name), flush=True)
        current = summarize(args.root)
        if not args.follow or current["complete_collection"]:
            break
        time.sleep(5)


if __name__ == "__main__":
    main()
