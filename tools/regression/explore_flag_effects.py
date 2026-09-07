#!/usr/bin/env python3
from __future__ import annotations

import argparse
import difflib
import json
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"

COMMON_NOTILE = [
    "--notile",
    "--smartfuse",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--nounrolljam",
    "--noparallel",
    "--rar",
]

COMMON_TILED = [
    "--tile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--rar",
    "--nodiamond-tile",
    "--noparallel",
]


@dataclass(frozen=True)
class FlagPair:
    name: str
    group: str
    baseline_args: tuple[str, ...]
    variant_args: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class Effect:
    fixture: str
    first_diff: str
    baseline_line: str
    variant_line: str
    diff_excerpt: list[str]


@dataclass(frozen=True)
class PairResult:
    name: str
    group: str
    description: str
    baseline_args: list[str]
    variant_args: list[str]
    searched_fixtures: int
    baseline_failures: int
    variant_failures: int
    timeouts: int
    effects: list[Effect]


PAIRS = [
    FlagPair(
        "dfp-vs-glpk",
        "lp-dfp",
        ("--notile", "--smartfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        ("--notile", "--smartfuse", "--glpk", "--dfp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "DFP scheduler mode compared with the GLPK affine baseline.",
    ),
    FlagPair(
        "typedfuse-vs-glpk",
        "lp-dfp",
        ("--notile", "--smartfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        ("--notile", "--typedfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "Typed fusion compared with the GLPK affine baseline.",
    ),
    FlagPair(
        "hybridfuse-vs-glpk",
        "lp-dfp",
        ("--notile", "--smartfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        ("--notile", "--smartfuse", "--glpk", "--hybridfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "Hybrid fusion compared with the GLPK affine baseline.",
    ),
    FlagPair(
        "delayedcut-vs-dfp",
        "lp-dfp",
        ("--notile", "--smartfuse", "--glpk", "--dfp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        ("--notile", "--smartfuse", "--glpk", "--dfp", "--delayedcut", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "Delayed-cut DFP compared with ordinary DFP.",
    ),
    FlagPair(
        "pipsolve-vs-smartfuse",
        "dependence-solver",
        tuple(COMMON_NOTILE),
        ("--notile", "--smartfuse", "--pipsolve", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "PIP solver selection compared with the default smart-fusion affine recipe.",
    ),
    FlagPair(
        "candldep-vs-smartfuse",
        "dependence-solver",
        tuple(COMMON_NOTILE),
        ("--notile", "--smartfuse", "--candldep", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "Candl dependence analysis compared with the default ISL dependence path.",
    ),
    FlagPair(
        "isldepaccesswise-vs-smartfuse",
        "dependence-solver",
        tuple(COMMON_NOTILE),
        ("--notile", "--smartfuse", "--isldepaccesswise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "ISL access-wise dependence extraction compared with the default dependence path.",
    ),
    FlagPair(
        "isldepstmtwise-vs-smartfuse",
        "dependence-solver",
        tuple(COMMON_NOTILE),
        ("--notile", "--smartfuse", "--isldepstmtwise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "ISL statement-wise dependence extraction compared with the default dependence path.",
    ),
    FlagPair(
        "isldepcoalesce-vs-smartfuse",
        "dependence-solver",
        tuple(COMMON_NOTILE),
        ("--notile", "--smartfuse", "--isldepcoalesce", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"),
        "ISL dependence coalescing compared with the default dependence path.",
    ),
    FlagPair(
        "intratileopt-vs-nointratileopt",
        "tiling",
        tuple(COMMON_TILED),
        ("--tile", "--smartfuse", "--intratileopt", "--noprevector", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel"),
        "Pluto intra-tile optimization compared with the default disabled route.",
    ),
    FlagPair(
        "partial-ft-lt-vs-full-tile",
        "tiling",
        tuple(COMMON_TILED),
        ("--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam", "--rar", "--ft=0", "--lt=1", "--nodiamond-tile", "--noparallel"),
        "Partial tiling-level control compared with full ordinary tiling.",
    ),
    FlagPair(
        "identity-iss-vs-identity",
        "identity-composition",
        ("--identity", "--tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"),
        ("--identity", "--tile", "--iss", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"),
        "ISS plus identity tiling compared with ordinary identity tiling.",
    ),
]


def optimized_loop(output: str) -> str:
    marker = "== Optimized Loop =="
    pos = output.find(marker)
    return output[pos:] if pos >= 0 else output


def run_polopt(args: tuple[str, ...], fixture: Path, timeout: int) -> tuple[int, str]:
    proc = subprocess.run(
        [str(POLOPT), "--pluto-compat", "--explain", *args, str(fixture)],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, optimized_loop(proc.stdout)


def first_diff(left: str, right: str) -> tuple[str, str, str]:
    left_lines = [line for line in left.splitlines() if line.strip()]
    right_lines = [line for line in right.splitlines() if line.strip()]
    for idx, (lhs, rhs) in enumerate(zip(left_lines, right_lines), start=1):
        if lhs != rhs:
            return f"line {idx}", lhs, rhs
    if len(left_lines) != len(right_lines):
        return f"line-count {len(left_lines)} -> {len(right_lines)}", "", ""
    return "different", "", ""


def diff_excerpt(left: str, right: str, context: int) -> list[str]:
    diff = list(
        difflib.unified_diff(
            left.splitlines(),
            right.splitlines(),
            fromfile="baseline",
            tofile="variant",
            lineterm="",
            n=context,
        )
    )
    return diff[:80]


def discover_fixtures(max_fixtures: int | None) -> list[Path]:
    roots = [
        ROOT / "tests" / "polopt-regression" / "inputs",
        ROOT / "tests" / "polopt-generated" / "inputs",
    ]
    fixtures: list[Path] = []
    for root in roots:
        fixtures.extend(sorted(root.glob("*.loop")))
    if max_fixtures is not None:
        return fixtures[:max_fixtures]
    return fixtures


def selected_pairs(names: set[str], groups: set[str]) -> list[FlagPair]:
    pairs = []
    for pair in PAIRS:
        if names and pair.name not in names:
            continue
        if groups and pair.group not in groups:
            continue
        pairs.append(pair)
    return pairs


def explore_pair(pair: FlagPair, fixtures: list[Path], limit: int, timeout: int, context: int) -> PairResult:
    effects: list[Effect] = []
    searched = 0
    baseline_failures = 0
    variant_failures = 0
    timeouts = 0
    for fixture in fixtures:
        searched += 1
        try:
            baseline_rc, baseline = run_polopt(pair.baseline_args, fixture, timeout)
            variant_rc, variant = run_polopt(pair.variant_args, fixture, timeout)
        except subprocess.TimeoutExpired:
            timeouts += 1
            continue
        if baseline_rc != 0:
            baseline_failures += 1
            continue
        if variant_rc != 0:
            variant_failures += 1
            continue
        if baseline == variant:
            continue
        where, lhs, rhs = first_diff(baseline, variant)
        effects.append(
            Effect(
                fixture=str(fixture.relative_to(ROOT)),
                first_diff=where,
                baseline_line=lhs,
                variant_line=rhs,
                diff_excerpt=diff_excerpt(baseline, variant, context),
            )
        )
        if len(effects) >= limit:
            break
    return PairResult(
        name=pair.name,
        group=pair.group,
        description=pair.description,
        baseline_args=list(pair.baseline_args),
        variant_args=list(pair.variant_args),
        searched_fixtures=searched,
        baseline_failures=baseline_failures,
        variant_failures=variant_failures,
        timeouts=timeouts,
        effects=effects,
    )


def write_markdown(results: list[PairResult]) -> str:
    lines = [
        "# Pluto Flag Effect Exploration",
        "",
        "This report compares `polopt --pluto-compat --explain` optimized loops for paired Pluto-style flag sets.",
        "A reported effect means both commands succeeded and the optimized-loop text changed.",
        "",
        "| Pair | Group | Searched | Effects | Notes |",
        "|---|---|---:|---:|---|",
    ]
    for result in results:
        notes = []
        if result.timeouts:
            notes.append(f"{result.timeouts} timeouts")
        if result.baseline_failures:
            notes.append(f"{result.baseline_failures} baseline failures")
        if result.variant_failures:
            notes.append(f"{result.variant_failures} variant failures")
        lines.append(
            f"| `{result.name}` | {result.group} | {result.searched_fixtures} | {len(result.effects)} | {'; '.join(notes)} |"
        )
    for result in results:
        lines.extend(["", f"## {result.name}", "", result.description, ""])
        if not result.effects:
            lines.append("No optimized-loop effect was found in the searched fixtures.")
            continue
        for effect in result.effects:
            lines.extend(
                [
                    f"### `{effect.fixture}`",
                    "",
                    f"- first difference: {effect.first_diff}",
                    f"- baseline: `{effect.baseline_line}`",
                    f"- variant: `{effect.variant_line}`",
                    "",
                    "```diff",
                    *effect.diff_excerpt,
                    "```",
                    "",
                ]
            )
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pair", action="append", default=[], help="run only this pair name; may be repeated")
    ap.add_argument("--group", action="append", default=[], help="run only this group; may be repeated")
    ap.add_argument("--list", action="store_true", help="list available pairs and exit")
    ap.add_argument("--limit-per-pair", type=int, default=3)
    ap.add_argument("--max-fixtures", type=int)
    ap.add_argument("--timeout", type=int, default=25)
    ap.add_argument("--diff-context", type=int, default=3)
    ap.add_argument("--json-out", type=Path)
    ap.add_argument("--markdown-out", type=Path)
    args = ap.parse_args()

    if args.list:
        for pair in PAIRS:
            print(f"{pair.name}\t{pair.group}\t{pair.description}")
        return 0

    pairs = selected_pairs(set(args.pair), set(args.group))
    if not pairs:
        raise SystemExit("no matching flag-effect pairs")
    fixtures = discover_fixtures(args.max_fixtures)
    results = [
        explore_pair(pair, fixtures, args.limit_per_pair, args.timeout, args.diff_context)
        for pair in pairs
    ]
    data = {
        "root": str(ROOT),
        "fixture_count": len(fixtures),
        "pairs": [asdict(result) for result in results],
        "summary": {
            "pairs": len(results),
            "pairs_with_effects": sum(1 for result in results if result.effects),
            "effects": sum(len(result.effects) for result in results),
        },
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(data, indent=2, sort_keys=True))
    if args.markdown_out:
        args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
        args.markdown_out.write_text(write_markdown(results))
    if not args.json_out and not args.markdown_out:
        print(write_markdown(results), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
