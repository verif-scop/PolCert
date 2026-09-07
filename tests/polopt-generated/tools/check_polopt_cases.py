#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys


TILING_ROUTE_RE = re.compile(r"^\[tiling-validation\] route=([^\s]+)$", re.MULTILINE)
TILING_STATUS_RE = re.compile(
    r"^\[tiling-validation\] status=([^\s]+) reason=([^\s]+)$",
    re.MULTILINE,
)


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"manifest must be a JSON object: {path}")
    return data


def parse_status(path: pathlib.Path) -> dict[str, str]:
    data: dict[str, str] = {}
    for line in path.read_text().splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        data[key.strip()] = value.strip()
    return data


def check_case_dir(case_dir: pathlib.Path) -> tuple[bool, bool]:
    status_path = case_dir / "status.txt"
    if not status_path.exists():
        raise SystemExit(f"missing status.txt for case {case_dir.name}")
    status = parse_status(status_path)
    result = status.get("result")
    if result != "ok":
        return False, False
    changed = status.get("changed") == "true"
    return True, changed


def check_tiling_validation(case_dir: pathlib.Path, expected: str) -> None:
    stderr_path = case_dir / "stderr.txt"
    if not stderr_path.exists():
        raise SystemExit(f"missing stderr.txt for case {case_dir.name}")
    stderr = stderr_path.read_text()
    if "[alarm]" in stderr:
        raise SystemExit(
            f"case {case_dir.name} emitted an alarm despite successful materialization"
        )
    if "fallback" in stderr.lower():
        raise SystemExit(
            f"case {case_dir.name} emitted forbidden fallback telemetry"
        )
    routes = TILING_ROUTE_RE.findall(stderr)
    statuses = TILING_STATUS_RE.findall(stderr)
    if expected in ("permutable-band", "actual-schedule"):
        if routes != [expected] or statuses:
            raise SystemExit(
                f"case {case_dir.name} has tiling evidence "
                f"routes={routes!r} statuses={statuses!r}, expected exactly one {expected} route"
            )
    elif expected == "not-applicable:no-loop":
        if routes or statuses != [("not-applicable", "no-loop")]:
            raise SystemExit(
                f"case {case_dir.name} has tiling evidence "
                f"routes={routes!r} statuses={statuses!r}, expected one no-loop not-applicable status"
            )
    else:
        raise SystemExit(
            f"unsupported tiling validation expectation {expected!r} for case {case_dir.name}"
        )


def loop_count(text: str) -> int:
    return text.count("for ")


def strip_outer_if(text: str) -> str:
    stripped = text.strip()
    while stripped.startswith("if "):
        start = stripped.find("{")
        if start < 0:
            break
        depth = 0
        end = None
        for index, ch in enumerate(stripped[start:], start):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None or end != len(stripped) - 1:
            break
        stripped = stripped[start + 1:end].strip()
    return stripped + "\n"


def alpha_normalize_loop_vars(text: str) -> str:
    loop_vars: list[str] = []
    for match in re.finditer(r"\bfor\s+([A-Za-z_][A-Za-z0-9_]*)\s+in\s+range\(", text):
        loop_var = match.group(1)
        if loop_var not in loop_vars:
            loop_vars.append(loop_var)
    normalized = text
    for index, loop_var in enumerate(loop_vars):
        normalized = re.sub(
            rf"\b{re.escape(loop_var)}\b",
            f"__iv{index}__",
            normalized,
        )
    return normalized


def is_nontrivially_changed(case_dir: pathlib.Path) -> bool:
    input_text = (case_dir / "input.pretty.loop").read_text()
    opt_text = (case_dir / "optimized.loop").read_text()
    normalized_input = alpha_normalize_loop_vars(strip_outer_if(input_text))
    normalized_opt = alpha_normalize_loop_vars(strip_outer_if(opt_text))
    return normalized_input != normalized_opt


def detect_tiled(case_dir: pathlib.Path) -> bool:
    input_path = case_dir / "input.pretty.loop"
    opt_path = case_dir / "optimized.loop"
    if not input_path.exists() or not opt_path.exists():
        raise SystemExit(f"missing loop dump(s) for case {case_dir.name}")
    input_text = input_path.read_text()
    opt_text = opt_path.read_text()
    return (
        loop_count(opt_text) >= loop_count(input_text) + 2
        and "max(" in opt_text
        and "min(" in opt_text
        and ("/ 32" in opt_text or "/32" in opt_text)
    )


def require_tiled(case_dir: pathlib.Path) -> None:
    opt_path = case_dir / "optimized.loop"
    if not opt_path.exists():
        raise SystemExit(f"missing optimized.loop for tiled case {case_dir.name}")
    if not detect_tiled(case_dir):
        input_text = (case_dir / "input.pretty.loop").read_text()
        opt_text = opt_path.read_text()
        raise SystemExit(
            "case "
            f"{case_dir.name} is not detected as tiled "
            f"(input_loops={loop_count(input_text)}, optimized_loops={loop_count(opt_text)})"
        )


def required_effect_failures(
    case_name: str,
    *,
    changed: bool,
    nontrivial_changed: bool,
    tiled: bool,
    require_nontrivial_changed: set[str],
    require_unchanged: set[str],
    require_tiled_cases: set[str],
) -> list[str]:
    failures: list[str] = []
    if case_name in require_nontrivial_changed and not nontrivial_changed:
        failures.append("expected a nontrivial optimized-loop change")
    if case_name in require_unchanged and changed:
        failures.append("expected the optimized loop to remain unchanged")
    if case_name in require_tiled_cases and not tiled:
        failures.append("expected explicit tiled bounds")
    return failures


def effect_expectation(
    case_name: str,
    *,
    require_nontrivial_changed: set[str],
    require_unchanged: set[str],
    require_tiled_cases: set[str],
) -> str:
    parts: list[str] = []
    if case_name in require_nontrivial_changed:
        parts.append("nontrivial-change")
    elif case_name in require_unchanged:
        parts.append("unchanged")
    else:
        parts.append("successful-materialization")
    if case_name in require_tiled_cases:
        parts.append("tiled")
    return "+".join(parts)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        default=None,
        help="JSON manifest with suite thresholds and required tiled cases",
    )
    parser.add_argument(
        "--cases-dir",
        default="tests/polopt-generated/cases",
        help="Directory containing materialized per-case outputs",
    )
    parser.add_argument(
        "--expect-total",
        type=int,
        default=None,
        help="Expected number of cases",
    )
    parser.add_argument(
        "--min-changed",
        type=int,
        default=0,
        help="Minimum number of successful cases that must differ from input",
    )
    parser.add_argument(
        "--min-nontrivial-changed",
        type=int,
        default=0,
        help="Minimum number of successful cases that must differ after alpha-normalization and outer-guard stripping",
    )
    parser.add_argument(
        "--require-tiled",
        nargs="*",
        default=[],
        help="Case names that must show explicit tiled bounds in optimized.loop",
    )
    args = parser.parse_args()

    manifest: dict[str, object] = {}
    if args.manifest is not None:
        manifest = load_manifest(pathlib.Path(args.manifest))

    cases_dir = pathlib.Path(str(manifest.get("cases_dir", args.cases_dir)))
    if args.cases_dir != parser.get_default("cases_dir"):
        cases_dir = pathlib.Path(args.cases_dir)
    expect_total = manifest.get("expect_total", args.expect_total)
    if args.expect_total is not None:
        expect_total = args.expect_total
    min_changed = int(manifest.get("min_changed", args.min_changed))
    if args.min_changed != parser.get_default("min_changed"):
        min_changed = args.min_changed
    min_nontrivial_changed = int(
        manifest.get("min_nontrivial_changed", args.min_nontrivial_changed)
    )
    if args.min_nontrivial_changed != parser.get_default("min_nontrivial_changed"):
        min_nontrivial_changed = args.min_nontrivial_changed
    require_tiled_cases = manifest.get("require_tiled", args.require_tiled)
    if args.require_tiled != parser.get_default("require_tiled"):
        require_tiled_cases = args.require_tiled
    if not isinstance(require_tiled_cases, list) or not all(
        isinstance(case, str) for case in require_tiled_cases
    ):
        raise SystemExit("require_tiled must be a list of case names")
    require_nontrivial_changed_cases = manifest.get(
        "require_nontrivial_changed", []
    )
    require_unchanged_cases = manifest.get("require_unchanged", [])
    for key, value in (
        ("require_nontrivial_changed", require_nontrivial_changed_cases),
        ("require_unchanged", require_unchanged_cases),
    ):
        if not isinstance(value, list) or not all(
            isinstance(case, str) for case in value
        ):
            raise SystemExit(f"{key} must be a list of case names")
    require_nontrivial_changed_set = set(require_nontrivial_changed_cases)
    require_unchanged_set = set(require_unchanged_cases)
    require_tiled_set = set(require_tiled_cases)
    overlap = require_nontrivial_changed_set & require_unchanged_set
    if overlap:
        raise SystemExit(
            "cases cannot require both nontrivial change and unchanged output: "
            + ", ".join(sorted(overlap))
        )
    if expect_total is not None:
        expect_total = int(expect_total)
    tiling_validation = manifest.get("tiling_validation", None)
    default_tiling_validation: str | None = None
    tiling_validation_overrides: dict[str, str] = {}
    if tiling_validation is not None:
        if not isinstance(tiling_validation, dict):
            raise SystemExit("tiling_validation must be an object")
        default_tiling_validation = tiling_validation.get("default")
        raw_overrides = tiling_validation.get("overrides", {})
        if not isinstance(default_tiling_validation, str):
            raise SystemExit("tiling_validation.default must be a string")
        if not isinstance(raw_overrides, dict) or not all(
            isinstance(name, str) and isinstance(expected, str)
            for name, expected in raw_overrides.items()
        ):
            raise SystemExit("tiling_validation.overrides must map case names to strings")
        tiling_validation_overrides = raw_overrides

    cases_root = cases_dir
    if not cases_root.is_dir():
        raise SystemExit(f"cases dir not found: {cases_root}")

    case_dirs = sorted(
        p for p in cases_root.iterdir() if p.is_dir() and not p.name.startswith(".")
    )
    total = len(case_dirs)
    ok = 0
    changed = 0
    nontrivial_changed = 0
    failed: list[str] = []
    detected_tiled: list[str] = []
    tiling_validation_counts = {
        "permutable-band": 0,
        "not-applicable:no-loop": 0,
    }
    effect_failures: list[str] = []
    case_names = {case_dir.name for case_dir in case_dirs}
    required_names = (
        require_nontrivial_changed_set | require_unchanged_set | require_tiled_set
    )
    unknown_required = sorted(required_names - case_names)
    if unknown_required:
        raise SystemExit(
            "effect constraints name unknown cases: " + ", ".join(unknown_required)
        )

    for case_dir in case_dirs:
        case_ok, case_changed = check_case_dir(case_dir)
        if case_ok:
            ok += 1
            if default_tiling_validation is not None:
                expected_tiling_validation = tiling_validation_overrides.get(
                    case_dir.name,
                    default_tiling_validation,
                )
                check_tiling_validation(
                    case_dir,
                    expected_tiling_validation,
                )
                tiling_validation_counts[expected_tiling_validation] = (
                    tiling_validation_counts.get(expected_tiling_validation, 0) + 1
                )
            case_nontrivial_changed = False
            if case_changed:
                changed += 1
                case_nontrivial_changed = is_nontrivially_changed(case_dir)
                if case_nontrivial_changed:
                    nontrivial_changed += 1
            case_tiled = detect_tiled(case_dir)
            if case_tiled:
                detected_tiled.append(case_dir.name)
            case_effect_failures = required_effect_failures(
                case_dir.name,
                changed=case_changed,
                nontrivial_changed=case_nontrivial_changed,
                tiled=case_tiled,
                require_nontrivial_changed=require_nontrivial_changed_set,
                require_unchanged=require_unchanged_set,
                require_tiled_cases=require_tiled_set,
            )
            has_case_effect_contract = case_dir.name in required_names
            outcome = "PASS" if not case_effect_failures else "FAIL"
            print(
                f"[strict-effect] {outcome} case={case_dir.name} "
                f"expected={effect_expectation(case_dir.name, require_nontrivial_changed=require_nontrivial_changed_set, require_unchanged=require_unchanged_set, require_tiled_cases=require_tiled_set)} "
                f"coverage={'effect' if has_case_effect_contract else 'acceptance-only'} "
                f"actual=changed:{str(case_changed).lower()},"
                f"nontrivial:{str(case_nontrivial_changed).lower()},"
                f"tiled:{str(case_tiled).lower()} "
                "interpretation="
                + (
                    (
                        "declared-optimization-effect-matched"
                        if has_case_effect_contract
                        else "no-case-specific-effect-contract"
                    )
                    if not case_effect_failures
                    else ";".join(case_effect_failures).replace(" ", "-")
                )
            )
            effect_failures.extend(
                f"{case_dir.name}: {failure}" for failure in case_effect_failures
            )
        else:
            failed.append(case_dir.name)

    if expect_total is not None and total != expect_total:
        raise SystemExit(f"expected {expect_total} cases, saw {total}")
    if failed:
        raise SystemExit(f"failed cases: {', '.join(failed)}")
    if effect_failures:
        raise SystemExit("effect assertion failures: " + "; ".join(effect_failures))
    if changed < min_changed:
        raise SystemExit(f"expected at least {min_changed} changed cases, saw {changed}")
    if nontrivial_changed < min_nontrivial_changed:
        raise SystemExit(
            "expected at least "
            f"{min_nontrivial_changed} nontrivially changed cases, "
            f"saw {nontrivial_changed}"
        )

    print(f"total={total}")
    print(f"ok={ok}")
    print(f"fail={len(failed)}")
    print(f"changed={changed}")
    print(f"nontrivial_changed={nontrivial_changed}")
    print(f"detected_tiled={len(detected_tiled)}")
    if detected_tiled:
        print(f"detected_tiled_cases={','.join(detected_tiled)}")
    if require_tiled_cases:
        print(f"required_tiled_cases={','.join(require_tiled_cases)}")
    if require_nontrivial_changed_cases:
        print(
            "required_nontrivial_changed_cases="
            + ",".join(require_nontrivial_changed_cases)
        )
    if require_unchanged_cases:
        print("required_unchanged_cases=" + ",".join(require_unchanged_cases))
    if default_tiling_validation is not None:
        print("tiling_validation=direct-only")
        print(
            "tiling_validation_permutable_band="
            f"{tiling_validation_counts['permutable-band']}"
        )
        print(
            "tiling_validation_not_applicable_no_loop="
            f"{tiling_validation_counts['not-applicable:no-loop']}"
        )
        print("tiling_validation_fallback=0")


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise
