#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT_ROOT = ROOT / "tests" / "polopt-generated" / "inputs"

COMMON_FLAGS = (
    "--pluto-compat",
    "--smartfuse",
    "--nointratileopt",
    "--nounrolljam",
    "--nodiamond-tile",
)
PIPELINE_FLAGS = {
    "affine": ("--notile",),
    "tiled": ("--tile",),
}
MODE_FLAGS = {
    "sequential": ("--noprevector", "--noparallel"),
    "parallel": ("--noprevector", "--parallel", "--innerpar"),
    "vector": ("--prevector", "--noparallel"),
}


@dataclass(frozen=True)
class RunResult:
    status: str
    returncode: int | None
    elapsed_seconds: float
    optimized_loop: str
    scheduled_openscop: str
    tiled: bool
    parallel: bool
    vector: bool
    diagnostic: str


def section(output: str, start_marker: str, end_marker: str | None = None) -> str:
    start = output.find(start_marker)
    if start < 0:
        return ""
    if end_marker is None:
        return output[start:].strip()
    end = output.find(end_marker, start + len(start_marker))
    return output[start:].strip() if end < 0 else output[start:end].strip()


def run_policy(
    polopt: Path,
    fixture: Path,
    pipeline: str,
    mode: str,
    rar: bool,
    timeout: int,
    dump_schedule: bool,
) -> RunResult:
    flags = [*COMMON_FLAGS, *PIPELINE_FLAGS[pipeline], *MODE_FLAGS[mode]]
    if rar:
        flags.append("--rar")
    if dump_schedule:
        flags.append("--dump-scheduled-openscop")
    command = [str(polopt), *flags, str(fixture)]
    environment = os.environ.copy()
    environment.setdefault("COMPCERT_CONFIG", str(ROOT / "polcert.ini"))
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - started
        diagnostic = ((exc.stdout or "") + (exc.stderr or ""))[-1000:]
        return RunResult(
            "timeout", None, elapsed, "", "", False, False, False, diagnostic
        )

    elapsed = time.monotonic() - started
    output = proc.stdout + proc.stderr
    optimized = section(proc.stdout, "== Optimized Loop ==")
    scheduled = section(
        proc.stdout, "== Scheduled OpenScop ==", "== Optimized Loop =="
    )
    status = "accepted" if proc.returncode == 0 and optimized else "rejected"
    diagnostic = "\n".join(output.strip().splitlines()[-8:])
    return RunResult(
        status=status,
        returncode=proc.returncode,
        elapsed_seconds=elapsed,
        optimized_loop=optimized,
        scheduled_openscop=scheduled,
        tiled="[tiling-validation] route=permutable-band" in output,
        parallel="parallel for " in optimized,
        vector="vector for " in optimized,
        diagnostic=diagnostic,
    )


def pair_class(no_rar: RunResult, rar: RunResult) -> str:
    if no_rar.status == "timeout" or rar.status == "timeout":
        return "timeout"
    if no_rar.status == "accepted" and rar.status == "accepted":
        return "both-accepted"
    if no_rar.status == "accepted":
        return "no-rar-only"
    if rar.status == "accepted":
        return "rar-only"
    return "both-rejected"


def summarize(cases: list[dict[str, object]], mode: str) -> dict[str, object]:
    selected = [case for case in cases if case["mode"] == mode]
    classes = {
        name: sum(case["pair_class"] == name for case in selected)
        for name in (
            "both-accepted",
            "no-rar-only",
            "rar-only",
            "both-rejected",
            "timeout",
        )
    }
    both = [case for case in selected if case["pair_class"] == "both-accepted"]
    loop_different = sum(not case["optimized_loop_equal"] for case in both)
    schedule_compared = [case for case in both if case["schedule_compared"]]
    schedule_different = sum(
        not case["scheduled_openscop_equal"] for case in schedule_compared
    )
    no_rar_elapsed = sum(case["no_rar"]["elapsed_seconds"] for case in both)
    rar_elapsed = sum(case["rar"]["elapsed_seconds"] for case in both)
    timing_ratios = [
        case["rar"]["elapsed_seconds"] / case["no_rar"]["elapsed_seconds"]
        for case in both
        if case["no_rar"]["elapsed_seconds"] > 0
    ]
    return {
        "total": len(selected),
        **classes,
        "both_accepted_loop_equal": len(both) - loop_different,
        "both_accepted_loop_different": loop_different,
        "schedule_compared": len(schedule_compared),
        "schedule_different": schedule_different,
        "parallel_effect_changed": sum(
            case["no_rar"]["parallel"] != case["rar"]["parallel"]
            for case in both
        ),
        "vector_effect_changed": sum(
            case["no_rar"]["vector"] != case["rar"]["vector"]
            for case in both
        ),
        "checked_driver_no_rar_seconds": no_rar_elapsed,
        "checked_driver_rar_seconds": rar_elapsed,
        "checked_driver_aggregate_rar_over_no_rar": (
            rar_elapsed / no_rar_elapsed if no_rar_elapsed > 0 else None
        ),
        "checked_driver_median_case_rar_over_no_rar": (
            statistics.median(timing_ratios) if timing_ratios else None
        ),
        "checked_driver_mean_case_rar_over_no_rar": (
            statistics.fmean(timing_ratios) if timing_ratios else None
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compare checked PolOpt candidates with and without Pluto RAR relations."
    )
    parser.add_argument("--polopt", type=Path, default=ROOT / "polopt")
    parser.add_argument("--input-root", type=Path, default=DEFAULT_INPUT_ROOT)
    parser.add_argument(
        "--pipeline",
        choices=tuple(PIPELINE_FLAGS),
        default="tiled",
        help="compare the affine-only or the affine-plus-tiling route; default: tiled",
    )
    parser.add_argument(
        "--mode",
        action="append",
        choices=tuple(MODE_FLAGS),
        dest="modes",
        help="repeat to compare multiple routes; default: sequential",
    )
    parser.add_argument("--only", help="comma-separated fixture stems")
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--dump-schedule", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if not args.polopt.is_file():
        parser.error(f"missing PolOpt executable: {args.polopt}")
    fixtures = sorted(args.input_root.glob("*.loop"))
    if args.only:
        wanted = set(args.only.split(","))
        fixtures = [fixture for fixture in fixtures if fixture.stem in wanted]
        missing = sorted(wanted - {fixture.stem for fixture in fixtures})
        if missing:
            parser.error("unknown fixtures: " + ", ".join(missing))
    if not fixtures:
        parser.error(f"no .loop fixtures under {args.input_root}")

    modes = args.modes or ["sequential"]
    cases: list[dict[str, object]] = []
    for mode in modes:
        for fixture in fixtures:
            no_rar = run_policy(
                args.polopt,
                fixture,
                args.pipeline,
                mode,
                False,
                args.timeout,
                args.dump_schedule,
            )
            rar = run_policy(
                args.polopt,
                fixture,
                args.pipeline,
                mode,
                True,
                args.timeout,
                args.dump_schedule,
            )
            classification = pair_class(no_rar, rar)
            loop_equal = (
                no_rar.optimized_loop == rar.optimized_loop
                if classification == "both-accepted"
                else False
            )
            schedule_compared = bool(
                no_rar.scheduled_openscop and rar.scheduled_openscop
            )
            schedule_equal = (
                no_rar.scheduled_openscop == rar.scheduled_openscop
                if schedule_compared
                else False
            )
            case = {
                "name": fixture.stem,
                "pipeline": args.pipeline,
                "mode": mode,
                "pair_class": classification,
                "optimized_loop_equal": loop_equal,
                "schedule_compared": schedule_compared,
                "scheduled_openscop_equal": schedule_equal,
                "no_rar": asdict(no_rar),
                "rar": asdict(rar),
            }
            cases.append(case)
            print(
                f"[rar-compare] case={fixture.stem} pipeline={args.pipeline} mode={mode} "
                f"acceptance={classification} "
                f"loop={'same' if loop_equal else 'different-or-unavailable'} "
                f"parallel={no_rar.parallel}->{rar.parallel} "
                f"vector={no_rar.vector}->{rar.vector}",
                flush=True,
            )

    summaries = {mode: summarize(cases, mode) for mode in modes}
    report = {
        "schema": 2,
        "rar_interpretation": (
            "RAR adds read-read reuse relations to Pluto's dependence-distance "
            "bounding objective. Pluto excludes them from legality and "
            "permutability constraints; PolCert validates either returned "
            "candidate independently."
        ),
        "timing_interpretation": (
            "Elapsed times cover the complete checked PolOpt invocation, not "
            "Pluto alone, and are descriptive rather than a stable benchmark."
        ),
        "pipeline": args.pipeline,
        "modes": modes,
        "summaries": summaries,
        "cases": cases,
    }
    for mode, summary in summaries.items():
        print(
            f"[rar-compare] SUMMARY pipeline={args.pipeline} mode={mode} "
            f"{json.dumps(summary, sort_keys=True)}",
            flush=True,
        )
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(f"[rar-compare] report={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
