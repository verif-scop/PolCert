#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
from collections import Counter


PIPELINE_CANON = {
    "precomputed": "default_no_iss_affine_tiling",
    "default_no_iss_affine_tiling": "default_no_iss_affine_tiling",
    "identity": "identity",
    "affine_only": "affine_only",
    "iss": "iss",
    "parallel_4": "parallel_4",
    "iss_parallel_4": "iss_parallel_4",
}

PIPELINE_LABEL = {
    "default_no_iss_affine_tiling": "default no-ISS affine+tiling pipeline",
    "identity": "identity-only fallback",
    "affine_only": "affine-only pipeline",
    "iss": "ISS-enabled sequential pipeline",
    "parallel_4": "parallel route (4 threads)",
    "iss_parallel_4": "ISS + parallel route (4 threads)",
}

PIPELINE_FLAGS = {
    "default_no_iss_affine_tiling": "(default)",
    "identity": "`--identity`",
    "affine_only": "`--affine-only`",
    "iss": "`--iss`",
    "parallel_4": "`--parallel` + `OMP_NUM_THREADS=4`",
    "iss_parallel_4": "`--iss --parallel` + `OMP_NUM_THREADS=4`",
}

def canonical_pipeline(name: str) -> str:
    return PIPELINE_CANON.get(name, name)


def load_json(path: pathlib.Path):
    return json.loads(path.read_text())


def make_table(summary: dict, report: dict) -> str:
    counts = Counter(canonical_pipeline(v) for v in summary["cases"].values())
    lines = []
    lines.append("# Best Generated Perf Pipelines")
    lines.append("")
    lines.append("This saved report reflects the supplied runtime-search records, not a measurement of the current checkout. See [the harness guide](README.md) before reusing these choices.")
    lines.append("")
    lines.append("Notes:")
    lines.append("")
    lines.append("- Baseline is always the unoptimized `input.loop` compiled into the same generated whole-C harness.")
    lines.append("- Every selected optimized result goes through `polopt`; baseline is **not** eligible as a best pipeline.")
    lines.append("- `identity` is only a last-resort `polopt --identity` fallback when all real optimization routes are slower.")
    lines.append("- Values are generated-executable runtimes on the recorded parameters and machine, not compiler timings.")
    lines.append("- In these records, `iss` / `iss_parallel_4` means the `--iss` route measured best; it does **not** by itself prove that Pluto actually performed ISS statement splitting on that case.")
    lines.append("")
    lines.append("## Pipeline Counts")
    lines.append("")
    for key in [
        "default_no_iss_affine_tiling",
        "affine_only",
        "iss",
        "parallel_4",
        "iss_parallel_4",
        "identity",
    ]:
        lines.append(f"- {PIPELINE_LABEL[key]}: `{counts.get(key, 0)}`")
    lines.append("")
    lines.append("## Per-Case Table")
    lines.append("")
    lines.append("| Case | Selected pipeline | Flags | Speedup | Optimized time (s) | Parallel annotation |")
    lines.append("|---|---|---|---:|---:|---|")
    for case in sorted(report):
        best = report[case]["best_pipeline"]
        best = canonical_pipeline(best)
        cand = next(
            c for c in report[case]["candidates"] if canonical_pipeline(c["pipeline_name"]) == best
        )
        par = bool(cand["parallelized_loop"])
        lines.append(
            "| {case} | {pipe} | {flags} | {speedup:.3f}x | {opt:.4f} | {par} |".format(
                case=case,
                pipe=PIPELINE_LABEL[best],
                flags=PIPELINE_FLAGS[best],
                speedup=float(cand["speedup"]),
                opt=float(cand["optimized_best_seconds"]),
                par="yes" if par else "no",
            )
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--summary-in", required=True)
    ap.add_argument("--report-in", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    summary_path = pathlib.Path(args.summary_in)
    report_path = pathlib.Path(args.report_in)
    out_path = pathlib.Path(args.output)

    summary = load_json(summary_path)
    report = load_json(report_path)
    out_path.write_text(make_table(summary, report))
    print(f"[E2E-GEN-REPORT] OK {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
