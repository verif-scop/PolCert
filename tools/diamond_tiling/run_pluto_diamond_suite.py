#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
POLCERT = ROOT / "polcert"
PLUTO = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
PLUTO_TEST_DIR = Path(os.environ.get("PLUTO_TEST_DIR", "/pluto/test"))

COMMON_PLUTO_FLAGS = [
    "--silent",
    "--dumpscop",
    "--rar",
    "--tile",
    "--noparallel",
    "--nointratileopt",
    "--nounrolljam",
    "--noprevector",
]

SUPPORTED_CASES: dict[str, dict[str, object]] = {
    "diamond-tile-example.c": {"kind": "diamond", "phase_ok": True},
    "fdtd-2d.c": {"kind": "diamond", "phase_ok": True},
    "heat-3d-imperfect.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-1d-imper.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-2d-imper.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-2d.c": {"kind": "diamond", "phase_ok": True},
    "multi-stmt-stencil-seq.c": {"kind": "no_effect", "phase_ok": True},
    "seidel.c": {"kind": "no_effect", "phase_ok": True},
}

PRODUCER_REJECTED_CASES = {}

UNSUPPORTED_CASES = [
    "heat-2d.c",
    "heat-2dp.c",
    "heat-3d.c",
    "jacobi-1d-mod.c",
    "jacobi-1d-periodic-even.c",
    "jacobi-1d-periodic.c",
    "jacobi-2d-17pt.c",
    "jacobi-2d-imper.par2d.c",
    "jacobi-2d-periodic.c",
    "jacobi-3d-25pt.c",
    "jacobi-3d-periodic.c",
]

PHASE_TILING_ROUTE_RE = re.compile(
    r"^\[PHASE\] tiling\(mid, posttile\): (OK|FAIL) route=([^\s]+)$",
    re.MULTILINE,
)


def run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd is not None else None,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def require_file(path: Path) -> None:
    if not path.exists():
        raise AssertionError(f"missing expected file: {path}")


def witness_has_mixed_affine(text: str) -> bool:
    for line in text.splitlines():
        if "tile link:" not in line or "floor(" not in line or "/" not in line:
            continue
        expr = line.split("floor(", 1)[1].split("/", 1)[0]
        if "+" in expr or "-" in expr[1:]:
            return True
    return False


def contains_fallback_marker(*texts: str) -> bool:
    return any("fallback" in text.lower() for text in texts)


def phase_validation_succeeds(text: str, expected_route: str) -> bool:
    return (
        "[PHASE] affine(before, mid): OK" in text
        and PHASE_TILING_ROUTE_RE.findall(text) == [("OK", expected_route)]
        and "[PHASE] affine(posttile, after): OK" in text
        and "[OK] Diamond phase-aligned validation succeeded" in text
        and not contains_fallback_marker(text)
    )


def phase_validation_rejects_tiling(text: str) -> bool:
    return (
        "[PHASE] affine(before, mid): OK" in text
        and PHASE_TILING_ROUTE_RE.findall(text) == [("FAIL", "rejected")]
        and "[PHASE] affine(posttile, after): OK" in text
        and "[FAIL] Diamond phase-aligned validation failed" in text
        and not contains_fallback_marker(text)
    )


def first_nonempty_line(text: str) -> str:
    for line in text.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped
    return ""


def classify_pluto_rejection(result: dict[str, object]) -> tuple[str, str]:
    if result["timed_out"]:
        return ("timeout", "Pluto timed out")
    stderr = str(result["stderr"])
    stdout = str(result["stdout"])
    combined = stderr + "\n" + stdout
    if "[Clan] Error:" in combined or "Error extracting polyhedra" in combined:
        reason = first_nonempty_line(stderr) or "Error extracting polyhedra from source file"
        return ("pluto_frontend_rejected", reason)
    if result["returncode"] != 0:
        reason = first_nonempty_line(stderr) or first_nonempty_line(stdout)
        return ("pluto_rejected", reason or f"Pluto exited with {result['returncode']}")
    return ("unexpected_success", "")


def run_pluto_case(
    case_name: str,
    case_root: Path,
    *,
    diamond: bool,
    timeout: int,
) -> dict[str, object]:
    mode = "diamond" if diamond else "nodiamond"
    run_root = case_root / mode
    run_root.mkdir(parents=True, exist_ok=True)
    src = PLUTO_TEST_DIR / case_name
    shutil.copy2(src, run_root / case_name)

    extra_flag = "--diamond-tile" if diamond else "--nodiamond-tile"
    cmd = [str(PLUTO), *COMMON_PLUTO_FLAGS, extra_flag, case_name]
    try:
        proc = run(cmd, cwd=run_root, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
        timed_out = True

    write_text(run_root / "pluto.stdout.txt", proc.stdout)
    write_text(run_root / "pluto.stderr.txt", proc.stderr)

    stem = Path(case_name).stem
    before = run_root / f"{stem}.beforescheduling.scop"
    mid = run_root / f"{stem}.midtransform.scop"
    posttile = run_root / f"{stem}.posttile.scop"
    after = run_root / f"{stem}.afterscheduling.scop"

    return {
        "cmd": cmd,
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "before": before,
        "mid": mid,
        "posttile": posttile,
        "after": after,
        "root": run_root,
    }


def run_polopt(label: str, args: list[str], case_root: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    cmd = [str(POLOPT), *args]
    try:
        proc = run(cmd, cwd=ROOT, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
    write_text(case_root / f"{label}.stdout.txt", proc.stdout)
    write_text(case_root / f"{label}.stderr.txt", proc.stderr)
    return proc


def run_polcert_phase(before: Path, mid: Path, posttile: Path, after: Path, case_root: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    cmd = [str(POLCERT), str(before), str(mid), str(posttile), str(after)]
    try:
        proc = run(
            cmd,
            cwd=ROOT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
    write_text(case_root / "phase.stdout.txt", proc.stdout)
    write_text(case_root / "phase.stderr.txt", proc.stderr)
    return proc


def check_supported_case(case_name: str, expectation: dict[str, object], out_root: Path, timeout: int) -> tuple[dict[str, object], list[str]]:
    case_root = out_root / Path(case_name).stem
    failures: list[str] = []

    nodiamond = run_pluto_case(case_name, case_root, diamond=False, timeout=timeout)
    diamond = run_pluto_case(case_name, case_root, diamond=True, timeout=timeout)

    if nodiamond["returncode"] != 0:
        diagnostic = first_nonempty_line(str(nodiamond["stderr"])) or first_nonempty_line(
            str(nodiamond["stdout"])
        )
        failures.append(
            f"{case_name}: nodiamond Pluto failed with exit={nodiamond['returncode']}, "
            f"diagnostic={diagnostic or 'none'}"
        )
        return ({"case": case_name, "status": "error"}, failures)
    if diamond["returncode"] != 0:
        diagnostic = first_nonempty_line(str(diamond["stderr"])) or first_nonempty_line(
            str(diamond["stdout"])
        )
        failures.append(
            f"{case_name}: diamond Pluto failed with exit={diamond['returncode']}, "
            f"diagnostic={diagnostic or 'none'}"
        )
        return ({"case": case_name, "status": "error"}, failures)

    for key in ["before", "mid", "posttile", "after"]:
        require_file(diamond[key])  # type: ignore[index]
    require_file(nodiamond["mid"])  # type: ignore[arg-type]

    midpoint_changed = (
        Path(nodiamond["mid"]).read_bytes() != Path(diamond["mid"]).read_bytes()
    )
    observed_kind = "diamond" if midpoint_changed else "no_effect"
    expected_kind = str(expectation["kind"])
    expected_route = str(expectation.get("route", "permutable-band"))
    expects_tiling_acceptance = expected_route != "rejected"
    if observed_kind != expected_kind:
        failures.append(
            f"{case_name}: expected {expected_kind}, observed {observed_kind}"
        )

    affine = run_polopt(
        "affine",
        [
            "--validate-affine-openscop",
            str(diamond["before"]),
            str(diamond["mid"]),
        ],
        case_root,
        timeout,
    )
    if affine.returncode == 124:
        failures.append(f"{case_name}: affine validator timed out")
    elif affine.returncode != 0 or "overall: PASS" not in affine.stdout:
        failures.append(f"{case_name}: affine validator failed")

    tiling = run_polopt(
        "tiling",
        [
            "--validate-tiling-openscop",
            str(diamond["mid"]),
            str(diamond["posttile"]),
        ],
        case_root,
        timeout,
    )
    tiling_routes = [
        line.strip()
        for line in tiling.stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]
    if tiling.returncode == 124:
        failures.append(f"{case_name}: OpenScop tiling validator timed out")
    elif "overall: PASS" not in tiling.stdout:
        failures.append(f"{case_name}: structural tiling inspection failed")
    elif expects_tiling_acceptance and (
        tiling.returncode != 0 or "formal: PASS" not in tiling.stdout
    ):
        failures.append(f"{case_name}: OpenScop tiling validator failed")
    elif not expects_tiling_acceptance and (
        tiling.returncode == 0 or "formal: FAIL" not in tiling.stdout
    ):
        failures.append(f"{case_name}: expected a checked tiling rejection")
    elif tiling_routes != [f"[tiling-validation] route={expected_route}"]:
        failures.append(
            f"{case_name}: OpenScop tiling validator did not report exactly "
            f"one {expected_route} route"
        )
    elif contains_fallback_marker(tiling.stdout, tiling.stderr):
        failures.append(
            f"{case_name}: OpenScop tiling validator reported a fallback marker"
        )
    elif "[alarm]" in tiling.stderr:
        failures.append(f"{case_name}: OpenScop tiling validator reported an alarm")

    witness = run_polopt(
        "witness",
        [
            "--extract-tiling-witness-openscop",
            str(diamond["mid"]),
            str(diamond["posttile"]),
        ],
        case_root,
        timeout,
    )
    mixed_affine = witness_has_mixed_affine(witness.stdout)
    if witness.returncode == 124:
        failures.append(f"{case_name}: witness extraction timed out")
    elif witness.returncode != 0:
        failures.append(f"{case_name}: witness extraction failed")
    elif expected_kind == "diamond" and not mixed_affine:
        failures.append(f"{case_name}: witness did not expose a mixed affine diamond link")

    phase = run_polcert_phase(
        Path(diamond["before"]),
        Path(diamond["mid"]),
        Path(diamond["posttile"]),
        Path(diamond["after"]),
        case_root,
        timeout,
    )
    phase_output = phase.stdout + "\n" + phase.stderr
    phase_ok = phase_validation_succeeds(phase_output, expected_route)
    phase_rejected = phase_validation_rejects_tiling(phase_output)
    if phase.returncode == 124:
        failures.append(f"{case_name}: phase validator timed out")
    elif bool(expectation["phase_ok"]) and not phase_ok:
        failures.append(
            f"{case_name}: expected an accepted phase route, observed failure"
        )
    elif not bool(expectation["phase_ok"]) and not phase_rejected:
        failures.append(
            f"{case_name}: expected an explicit checked tiling rejection"
        )

    result = {
        "case": case_name,
        "status": observed_kind,
        "midpoint_changed": midpoint_changed,
        "affine_ok": affine.returncode == 0 and "overall: PASS" in affine.stdout,
        "tiling_ok": expects_tiling_acceptance and tiling.returncode == 0,
        "tiling_route": expected_route,
        "witness_mixed_affine": mixed_affine,
        "phase_ok": phase_ok,
    }
    return (result, failures)


def check_unsupported_case(case_name: str, out_root: Path, timeout: int) -> tuple[dict[str, object], list[str]]:
    case_root = out_root / Path(case_name).stem
    failures: list[str] = []
    diamond = run_pluto_case(case_name, case_root, diamond=True, timeout=timeout)
    status, reason = classify_pluto_rejection(diamond)
    if status != "pluto_frontend_rejected" or diamond["returncode"] != 8:
        failures.append(
            f"{case_name}: expected Pluto frontend rejection with exit=8, "
            f"observed status={status},exit={diamond['returncode']}"
        )
    result = {
        "case": case_name,
        "status": status,
        "reason": reason,
        "returncode": diamond["returncode"],
        "timed_out": diamond["timed_out"],
    }
    return (result, failures)


def check_producer_rejected_case(
    case_name: str,
    expectation: dict[str, object],
    out_root: Path,
    timeout: int,
) -> tuple[dict[str, object], list[str]]:
    case_root = out_root / Path(case_name).stem
    failures: list[str] = []
    nodiamond = run_pluto_case(case_name, case_root, diamond=False, timeout=timeout)
    diamond = run_pluto_case(case_name, case_root, diamond=True, timeout=timeout)
    expected_returncode = int(expectation["returncode"])
    expected_diagnostic = str(expectation["diagnostic"])
    combined = str(diamond["stderr"]) + "\n" + str(diamond["stdout"])
    diagnostic_lines = [line.strip() for line in combined.splitlines() if line.strip()]
    actual_diagnostic = next(
        (line for line in diagnostic_lines if "ERROR:" in line),
        diagnostic_lines[0] if diagnostic_lines else "none",
    )
    generated_c = Path(diamond["root"]) / f"{Path(case_name).stem}.pluto.c"
    afterschedule = Path(diamond["after"])

    if nodiamond["returncode"] != 0:
        failures.append(
            f"{case_name}: no-diamond control failed with exit={nodiamond['returncode']}"
        )
    if diamond["returncode"] != expected_returncode:
        failures.append(
            f"{case_name}: expected diamond exit={expected_returncode}, "
            f"observed exit={diamond['returncode']}"
        )
    if expected_diagnostic not in combined:
        failures.append(
            f"{case_name}: missing producer diagnostic: {expected_diagnostic}"
        )
    if generated_c.exists():
        failures.append(f"{case_name}: rejected producer emitted {generated_c.name}")
    if afterschedule.exists():
        failures.append(f"{case_name}: rejected producer emitted {afterschedule.name}")

    matched_rejection = (
        diamond["returncode"] == expected_returncode
        and expected_diagnostic in combined
        and not generated_c.exists()
        and not afterschedule.exists()
    )

    result = {
        "case": case_name,
        "status": (
            "pluto_final_schedule_rejected"
            if matched_rejection
            else "unexpected_producer_result"
        ),
        "returncode": diamond["returncode"],
        "diagnostic": actual_diagnostic,
        "nodiamond_ok": nodiamond["returncode"] == 0,
        "generated_c": generated_c.exists(),
        "afterscheduling_scop": afterschedule.exists(),
    }
    return (result, failures)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout-seconds", type=int, default=180)
    ap.add_argument("--keep-artifacts", action="store_true")
    ap.add_argument("--output-root")
    args = ap.parse_args()

    if not POLOPT.exists():
        print(f"[diamond-suite] missing executable: {POLOPT}", file=sys.stderr)
        return 2
    if not POLCERT.exists():
        print(f"[diamond-suite] missing executable: {POLCERT}", file=sys.stderr)
        return 2
    if not PLUTO.exists():
        print(f"[diamond-suite] missing Pluto binary: {PLUTO}", file=sys.stderr)
        return 2
    if not PLUTO_TEST_DIR.exists():
        print(f"[diamond-suite] missing Pluto test directory: {PLUTO_TEST_DIR}", file=sys.stderr)
        return 2

    if args.output_root:
        out_root = Path(args.output_root).resolve()
        if out_root.exists():
            shutil.rmtree(out_root)
        out_root.mkdir(parents=True, exist_ok=True)
        cleanup_root = False
    else:
        out_root = Path(tempfile.mkdtemp(prefix="polcert-diamond-suite-"))
        cleanup_root = not args.keep_artifacts

    failures: list[str] = []
    results: list[dict[str, object]] = []

    try:
        for case_name, expectation in SUPPORTED_CASES.items():
            result, case_failures = check_supported_case(
                case_name,
                expectation,
                out_root,
                args.timeout_seconds,
            )
            results.append(result)
            failures.extend(case_failures)
            expected_kind = str(expectation["kind"])
            expected_route = str(expectation.get("route", "permutable-band"))
            print(
                f"[diamond-suite] {'PASS' if not case_failures else 'FAIL'} case={case_name} "
                f"expected=effect:{expected_kind},route:{expected_route},phase:{str(expectation['phase_ok']).lower()} "
                f"actual=effect:{result['status']},affine:{str(result.get('affine_ok')).lower()},"
                f"tiling:{str(result.get('tiling_ok')).lower()},phase:{str(result.get('phase_ok')).lower()} "
                "interpretation="
                + (
                    "diamond-effect-and-three-phase-contract-matched"
                    if not case_failures
                    else "diamond-effect-or-validation-phase-did-not-match"
                )
            )

        for case_name, expectation in PRODUCER_REJECTED_CASES.items():
            result, case_failures = check_producer_rejected_case(
                case_name,
                expectation,
                out_root,
                args.timeout_seconds,
            )
            results.append(result)
            failures.extend(case_failures)
            print(
                f"[diamond-suite] {'PASS' if not case_failures else 'FAIL'} case={case_name} "
                f"expected=status:pluto_final_schedule_rejected,exit:{expectation['returncode']} "
                f"actual=status:{result['status']},exit:{result['returncode']} "
                "interpretation="
                + (
                    "fixed-producer-refused-an-illegal-final-schedule"
                    if not case_failures
                    else "producer-rejection-did-not-match-the-fixed-baseline"
                )
            )

        for case_name in UNSUPPORTED_CASES:
            result, case_failures = check_unsupported_case(
                case_name,
                out_root,
                args.timeout_seconds,
            )
            results.append(result)
            failures.extend(case_failures)
            print(
                f"[diamond-suite] {'PASS' if not case_failures else 'FAIL'} case={case_name} "
                "expected=status:pluto_frontend_rejected,exit:8 "
                f"actual=status:{result['status']},exit:{result.get('returncode')} "
                "interpretation="
                + (
                    "unsupported-input-was-rejected"
                    if not case_failures
                    else "unsupported-input-did-not-produce-declared-frontend-rejection"
                )
            )

        summary = {
            "pluto": str(PLUTO),
            "pluto_test_dir": str(PLUTO_TEST_DIR),
            "results": results,
            "failures": failures,
        }
        write_text(out_root / "summary.json", json.dumps(summary, indent=2, sort_keys=True))

        if failures:
            print("[diamond-suite] FAIL")
            for failure in failures:
                print(f"  - {failure}")
            print(f"[diamond-suite] artifacts: {out_root}")
            cleanup_root = False
            return 1

        print(
            f"[diamond-suite] PASS expected={len(results)} actual={len(results)} "
            "interpretation=all-declared-diamond-effects-and-rejections-matched"
        )
        return 0
    finally:
        if cleanup_root:
            shutil.rmtree(out_root, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
