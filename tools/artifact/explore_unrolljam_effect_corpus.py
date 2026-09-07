#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
from dataclasses import asdict, dataclass, replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
PLUTO = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))


DEFAULT_CASES = [
    "matmul.loop",
    "matmul-init.loop",
    "matmul-seq.loop",
    "mxv.loop",
    "mxv-seq.loop",
    "nodep.loop",
    "fusion1.loop",
    "fusion2.loop",
    "fusion7.loop",
    "fdtd-1d.loop",
    "jacobi-1d-imper.loop",
]

PLUTO_BASE_FLAGS = [
    "--dumpscop",
    "--readscop",
    "--tile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--nodiamond-tile",
    "--noparallel",
]

POLOPT_BASE_FLAGS = [
    "--pluto-compat",
    "--explain",
    "--notile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--unrolljam",
    "--nodiamond-tile",
    "--noparallel",
]


@dataclass(frozen=True)
class ProcSummary:
    exit: int
    stdout_path: str
    stderr_path: str
    stdout_tail: str
    stderr_tail: str
    timed_out: bool


@dataclass(frozen=True)
class CaseResult:
    fixture: str
    output_dir: str
    extract: ProcSummary
    pluto_nounrolljam: ProcSummary | None
    pluto_unrolljam: ProcSummary | None
    polopt_checked: ProcSummary | None
    after_scheduling_scops_equal: bool
    pluto_generated_c_differs: bool
    pluto_factor_marker_present: bool
    pluto_remainder_marker_present: bool
    pluto_codegen_unrolljam_effect: bool
    polopt_factor_marker_present: bool
    polopt_offset_marker_present: bool
    polopt_remainder_marker_present: bool
    polopt_checked_effect: bool
    polopt_tiling_route_absent: bool
    covered: bool
    note: str


def run(
    cmd: list[str],
    *,
    cwd: Path = ROOT,
    timeout: int = 60,
    stdout_path: Path,
    stderr_path: Path,
) -> ProcSummary:
    def text_of(data: str | bytes | None) -> str:
        if data is None:
            return ""
        if isinstance(data, bytes):
            return data.decode(errors="replace")
        return data

    stdout_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        stdout = text_of(proc.stdout)
        stderr = text_of(proc.stderr)
        returncode = proc.returncode
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        stdout = text_of(exc.stdout)
        stderr = text_of(exc.stderr) + f"\n[unrolljam-corpus] timeout after {timeout} seconds\n"
        returncode = 124
        timed_out = True
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    return ProcSummary(
        exit=returncode,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
        stdout_tail=stdout[-1200:],
        stderr_tail=stderr[-1200:],
        timed_out=timed_out,
    )


def tiling_validation_route_absent(stderr_path: str) -> bool:
    try:
        stderr = Path(stderr_path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    return "[tiling-validation]" not in stderr


def safe_name(path: Path) -> str:
    rel = display_path(path)
    return re.sub(r"[^A-Za-z0-9_.-]+", "__", rel)


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def resolve_case(case: str) -> Path:
    raw = Path(case)
    candidates: list[Path] = []
    if raw.is_absolute():
        candidates.append(raw)
    else:
        rel = raw if raw.suffix else raw.with_suffix(".loop")
        candidates.extend(
            [
                ROOT / rel,
                ROOT / "tests" / "polopt-generated" / "inputs" / rel.name,
                ROOT / "tests" / "polopt-regression" / "inputs" / rel.name,
            ]
        )
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    raise FileNotFoundError(case)


def export_scop(fixture: Path, case_dir: Path, timeout: int) -> tuple[ProcSummary, Path | None]:
    proc = run(
        [str(POLOPT), "--dump-extracted-openscop", "--extract-only", str(fixture)],
        timeout=timeout,
        stdout_path=case_dir / "extract.stdout.scop",
        stderr_path=case_dir / "extract.stderr.txt",
    )
    if proc.exit != 0:
        return proc, None
    scop = case_dir / (fixture.stem + ".scop")
    scop.write_text((case_dir / "extract.stdout.scop").read_text())
    return proc, scop


def run_pluto_codegen(
    scop: Path,
    case_dir: Path,
    *,
    mode: str,
    unrolljam: bool,
    factor: int,
    timeout: int,
) -> tuple[ProcSummary, str, str]:
    run_dir = case_dir / mode
    run_dir.mkdir(parents=True, exist_ok=True)
    local_scop = run_dir / scop.name
    shutil.copyfile(scop, local_scop)
    flags = list(PLUTO_BASE_FLAGS)
    if unrolljam:
        flags.extend(["--unrolljam", f"--ufactor={factor}"])
    else:
        flags.append("--nounrolljam")
    proc = run(
        [str(PLUTO), *flags, local_scop.name],
        cwd=run_dir,
        timeout=timeout,
        stdout_path=run_dir / "pluto.stdout.txt",
        stderr_path=run_dir / "pluto.stderr.txt",
    )
    c_path = Path(str(local_scop) + ".pluto.c")
    after_path = Path(str(local_scop) + ".afterscheduling.scop")
    return (
        proc,
        c_path.read_text() if c_path.exists() else "",
        after_path.read_text() if after_path.exists() else "",
    )


def optimized_loop(stdout: str) -> str:
    marker = "== Optimized Loop =="
    pos = stdout.find(marker)
    return stdout[pos:] if pos >= 0 else stdout


def run_polopt_checked(fixture: Path, case_dir: Path, *, factor: int, timeout: int) -> tuple[ProcSummary, str]:
    args = [str(POLOPT), *POLOPT_BASE_FLAGS, f"--ufactor={factor}", str(fixture)]
    proc = run(
        args,
        timeout=timeout,
        stdout_path=case_dir / "polopt.stdout.txt",
        stderr_path=case_dir / "polopt.stderr.txt",
    )
    return proc, optimized_loop((case_dir / "polopt.stdout.txt").read_text())


def native_factor_marker(c_text: str, factor: int) -> bool:
    return re.search(rf"\+=\s*{factor}\b", c_text) is not None


def native_remainder_marker(c_text: str) -> bool:
    return re.search(r"for\s*\(\s*;\s*[^;]+;\s*[^)]*\+\+", c_text) is not None


def polopt_factor_marker(loop_text: str, factor: int) -> bool:
    return (
        re.search(rf"\({factor}\s*\*\s*i[0-9]+\)", loop_text) is not None
        or re.search(rf"\({factor}\s*\*\s*\(", loop_text) is not None
    )


def polopt_offset_marker(loop_text: str, factor: int) -> bool:
    if factor <= 1:
        return False
    return re.search(rf"\+\s*{factor - 1}\)", loop_text) is not None


def polopt_remainder_marker(loop_text: str, factor: int) -> bool:
    return "range(" in loop_text and re.search(rf"/\s*{factor}\)", loop_text) is not None


def classify_note(result: CaseResult) -> str:
    if result.extract.exit != 0:
        return "extract failed"
    if result.pluto_nounrolljam is None or result.pluto_unrolljam is None:
        return "pluto not run"
    if result.pluto_nounrolljam.exit != 0 or result.pluto_unrolljam.exit != 0:
        return "pluto failed"
    if not result.pluto_codegen_unrolljam_effect:
        if result.polopt_checked_effect:
            return "native Pluto shows no clean direct effect; PolOpt applies an additional checked block/jam effect"
        if result.pluto_generated_c_differs:
            return "pluto changed C, but not as a clean codegen-only unroll-jam marker"
        return "native Pluto shows no direct unroll-jam C effect"
    if result.polopt_checked is None or result.polopt_checked.exit != 0:
        return "native effect exists; PolOpt checked route rejected"
    if not result.polopt_checked_effect:
        return "native effect exists; PolOpt accepted but no checked block/jam marker was detected"
    return "native effect covered by checked PolOpt structure"


def evaluate_case(fixture: Path, out_root: Path, *, factor: int, timeout: int) -> CaseResult:
    case_dir = out_root / safe_name(fixture)
    case_dir.mkdir(parents=True, exist_ok=True)
    extract_proc, scop = export_scop(fixture, case_dir, timeout)
    pluto_nounroll_proc: ProcSummary | None = None
    pluto_unroll_proc: ProcSummary | None = None
    polopt_proc: ProcSummary | None = None
    nounroll_c = ""
    unroll_c = ""
    nounroll_after = ""
    unroll_after = ""
    polopt_loop = ""

    if extract_proc.exit == 0 and scop is not None:
        pluto_nounroll_proc, nounroll_c, nounroll_after = run_pluto_codegen(
            scop,
            case_dir,
            mode="nounrolljam",
            unrolljam=False,
            factor=factor,
            timeout=timeout,
        )
        pluto_unroll_proc, unroll_c, unroll_after = run_pluto_codegen(
            scop,
            case_dir,
            mode="unrolljam",
            unrolljam=True,
            factor=factor,
            timeout=timeout,
        )
        polopt_proc, polopt_loop = run_polopt_checked(fixture, case_dir, factor=factor, timeout=timeout)

    after_same = bool(nounroll_after) and nounroll_after == unroll_after
    code_differs = bool(nounroll_c or unroll_c) and nounroll_c != unroll_c
    native_factor = native_factor_marker(unroll_c, factor)
    native_remainder = native_remainder_marker(unroll_c)
    native_effect = (
        pluto_nounroll_proc is not None
        and pluto_unroll_proc is not None
        and pluto_nounroll_proc.exit == 0
        and pluto_unroll_proc.exit == 0
        and after_same
        and code_differs
        and native_factor
    )
    polopt_factor = polopt_factor_marker(polopt_loop, factor)
    polopt_offset = polopt_offset_marker(polopt_loop, factor)
    polopt_remainder = polopt_remainder_marker(polopt_loop, factor)
    polopt_tiling_route_absent = (
        polopt_proc is not None
        and tiling_validation_route_absent(polopt_proc.stderr_path)
    )
    polopt_effect = (
        polopt_proc is not None
        and polopt_proc.exit == 0
        and polopt_factor
        and polopt_offset
        and polopt_tiling_route_absent
    )
    partial = CaseResult(
        fixture=display_path(fixture),
        output_dir=str(case_dir),
        extract=extract_proc,
        pluto_nounrolljam=pluto_nounroll_proc,
        pluto_unrolljam=pluto_unroll_proc,
        polopt_checked=polopt_proc,
        after_scheduling_scops_equal=after_same,
        pluto_generated_c_differs=code_differs,
        pluto_factor_marker_present=native_factor,
        pluto_remainder_marker_present=native_remainder,
        pluto_codegen_unrolljam_effect=native_effect,
        polopt_factor_marker_present=polopt_factor,
        polopt_offset_marker_present=polopt_offset,
        polopt_remainder_marker_present=polopt_remainder,
        polopt_checked_effect=polopt_effect,
        polopt_tiling_route_absent=polopt_tiling_route_absent,
        covered=(not native_effect) or polopt_effect,
        note="",
    )
    return replace(partial, note=classify_note(partial))


def write_markdown(payload: dict[str, object]) -> str:
    lines = [
        "# Direct Pluto Unroll-Jam Effect Corpus",
        "",
        "This report compares native Pluto `--unrolljam` against native Pluto `--nounrolljam` on extracted OpenScop, then checks whether the affine-validated `polopt --pluto-compat --notile --unrolljam` route produces a corresponding checked Loop-IR structure.",
        "",
        "A case counts as a direct Pluto codegen effect only when the two native Pluto after-scheduling OpenScop files are identical, the generated C differs, and the unrolled native C contains the requested factor step. PolOpt coverage is structural: its output must contain the same block factor and the final intra-block offset. The PolOpt side deliberately disables tiling, and any tiling-validation route report fails this check, so the result isolates the Loop-level unroll-jam implementation from tiling acceptance. The extracted sequential endpoint covers constant and block unrolling, locally validated jam, recursive composition, and cleanup.",
        "",
        "## Summary",
        "",
    ]
    summary = payload["summary"]  # type: ignore[index]
    for key in [
        "cases",
        "extract_failures",
        "pluto_failures",
        "native_codegen_effects",
        "native_effects_covered",
        "native_effects_uncovered",
        "polopt_tiling_route_reports",
        "polopt_extra_checked_effects_without_native",
        "native_no_effect",
    ]:
        lines.append(f"- {key}: {summary[key]}")  # type: ignore[index]
    lines.extend(
        [
            "",
            "## Cases",
            "",
            "| Fixture | Pluto clean codegen effect | PolOpt checked effect | Covered | Note |",
            "|---|---:|---:|---:|---|",
        ]
    )
    for row in payload["cases"]:  # type: ignore[index]
        lines.append(
            "| `{fixture}` | {native} | {polopt} | {covered} | {note} |".format(
                fixture=row["fixture"],
                native="yes" if row["pluto_codegen_unrolljam_effect"] else "no",
                polopt="yes" if row["polopt_checked_effect"] else "no",
                covered="yes" if row["covered"] else "no",
                note=row["note"],
            )
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-root", type=Path, default=Path("/tmp/polcert-unrolljam-effect-corpus"))
    ap.add_argument("--factor", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--case", action="append", dest="cases", help="Fixture path or basename. May be repeated.")
    ap.add_argument("--limit", type=int, help="Limit the selected case list after resolution.")
    args = ap.parse_args()

    if args.factor <= 1:
        raise SystemExit("--factor must be greater than 1")

    out_root = args.output_root.resolve()
    out_root.mkdir(parents=True, exist_ok=True)
    selected = args.cases if args.cases else DEFAULT_CASES
    fixtures = [resolve_case(case) for case in selected]
    if args.limit is not None:
        fixtures = fixtures[: args.limit]

    results = [evaluate_case(fixture, out_root, factor=args.factor, timeout=args.timeout) for fixture in fixtures]
    extract_failures = sum(1 for item in results if item.extract.exit != 0)
    pluto_failures = sum(
        1
        for item in results
        if item.extract.exit == 0
        and (
            item.pluto_nounrolljam is None
            or item.pluto_unrolljam is None
            or item.pluto_nounrolljam.exit != 0
            or item.pluto_unrolljam.exit != 0
        )
    )
    native_effects = [item for item in results if item.pluto_codegen_unrolljam_effect]
    uncovered = [item for item in native_effects if not item.covered]
    extra_polopt_effects = [
        item for item in results if not item.pluto_codegen_unrolljam_effect and item.polopt_checked_effect
    ]
    tiling_route_reports = [
        item for item in results if not item.polopt_tiling_route_absent
    ]
    summary = {
        "cases": len(results),
        "factor": args.factor,
        "extract_failures": extract_failures,
        "pluto_failures": pluto_failures,
        "native_codegen_effects": len(native_effects),
        "native_effects_covered": len(native_effects) - len(uncovered),
        "native_effects_uncovered": len(uncovered),
        "polopt_tiling_route_reports": len(tiling_route_reports),
        "polopt_extra_checked_effects_without_native": len(extra_polopt_effects),
        "native_no_effect": len([item for item in results if item.extract.exit == 0 and not item.pluto_codegen_unrolljam_effect]),
        "uncovered_fixtures": [item.fixture for item in uncovered],
        "polopt_extra_effect_fixtures": [item.fixture for item in extra_polopt_effects],
        "polopt_tiling_route_fixtures": [item.fixture for item in tiling_route_reports],
        "output_root": str(out_root),
    }
    payload = {
        "mode": "direct-pluto-unrolljam-effect-corpus",
        "summary": summary,
        "cases": [asdict(item) for item in results],
    }
    (out_root / "summary.json").write_text(json.dumps(payload, indent=2, sort_keys=True))
    (out_root / "summary.md").write_text(write_markdown(payload))
    print(json.dumps(summary, indent=2, sort_keys=True))

    ok = len(native_effects) > 0 and not uncovered and not tiling_route_reports
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
