"""Parse nested VPL intervals and check exclusive-time accounting."""
from collections import defaultdict
import re


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
