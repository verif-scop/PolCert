#!/usr/bin/env python3
"""Check representative cases through the complete direct-only tiling route."""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNTIME_ROUTE_RE = re.compile(
    r"^\[tiling-validation\] route=(permutable-band|actual-schedule|rejected)$",
    re.MULTILINE,
)
PAIR_ROUTE_RE = re.compile(r"\(route=(permutable-band|actual-schedule|rejected)\)")

REQUIRED_CASE_NAMES = {
    "ordinary-common-band",
    "second-level-zero-row-band",
    "second-level-zero-row-band-iss",
    "ordinary-phase-separated-mixed-depth",
    "ordinary-phase-separated-mixed-depth-iss",
    "mixed-depth-semantic-band",
    "mixed-depth-semantic-band-iss",
    "second-level-mixed-depth-semantic-band",
    "second-level-mixed-depth-semantic-band-iss",
    "dependent-one-dimensional-band",
    "frozen-diamond-phase-pair",
    "frozen-nonpermutable-band",
    "outside-band-write-preserved",
    "outside-band-write-delayed",
    "explicit-ordinary-noloop",
    "explicit-ordinary-noloop-iss",
    "explicit-identity-noloop",
    "explicit-identity-noloop-iss",
    "explicit-diamond-noloop",
    "explicit-diamond-noloop-iss",
    "explicit-second-level-noloop",
    "explicit-second-level-noloop-iss",
}


def run_case(
    executable: pathlib.Path,
    args: list[str],
    expected_route: str,
    timeout: int,
    *,
    expect_optimized_output: bool,
    expect_rejection_alarm: bool,
) -> str | None:
    env = os.environ.copy()
    env.setdefault("COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini"))
    with tempfile.TemporaryDirectory(prefix="polcert-direct-band-") as tmp:
        try:
            proc = subprocess.run(
                [str(executable), *args],
                cwd=tmp,
                env=env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return f"timed out after {timeout}s: {' '.join(args)}"

    output = proc.stdout + proc.stderr
    if expected_route == "rejected":
        if proc.returncode == 0:
            return f"rejected route exited successfully: {' '.join(args)}\n{output}"
    elif proc.returncode != 0:
        return f"exit {proc.returncode}: {' '.join(args)}\n{output}"
    matches = RUNTIME_ROUTE_RE.findall(output)
    if not matches:
        matches = PAIR_ROUTE_RE.findall(output)
    if len(matches) != 1:
        return f"expected one production route, found {len(matches)}\n{output}"
    if matches[0] != expected_route:
        return (
            f"expected route={expected_route}, got route={matches[0]}: "
            f"{' '.join(args)}"
        )
    if "fallback" in output.lower():
        return f"fallback marker in direct-only route output: {' '.join(args)}"
    alarm = "[alarm] requested checked optimization was rejected"
    if expected_route == "rejected":
        if "== Optimized Loop ==" in proc.stdout:
            return f"rejected route emitted optimized output: {' '.join(args)}"
        expected_alarm_count = 1 if expect_rejection_alarm else 0
        if proc.stderr.count(alarm) != expected_alarm_count:
            return (
                f"rejected route must emit {expected_alarm_count} rejection "
                f"alarm(s): "
                f"{' '.join(args)}\n{output}"
            )
    else:
        has_optimized_output = "== Optimized Loop ==" in proc.stdout
        if has_optimized_output != expect_optimized_output:
            expectation = (
                "an optimized result"
                if expect_optimized_output
                else "validator-only output"
            )
            return (
                f"accepted route did not emit {expectation}: "
                f"{' '.join(args)}\n{output}"
            )
        if "[alarm]" in proc.stderr:
            return f"accepted route emitted an alarm: {' '.join(args)}\n{output}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polopt", default="./polopt")
    parser.add_argument("--polcert", default="./polcert")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    polopt = pathlib.Path(args.polopt).resolve()
    polcert = pathlib.Path(args.polcert).resolve()
    if not polopt.is_file():
        raise SystemExit(f"missing polopt: {polopt}")
    if not polcert.is_file():
        raise SystemExit(f"missing polcert: {polcert}")

    noloop = ROOT / "tests" / "polopt-regression" / "inputs" / "noloop.loop"
    explicit_tile_flags = (
        "--tile",
        "--smartfuse",
        "--nointratileopt",
        "--noprevector",
        "--nounrolljam",
        "--rar",
        "--nodiamond-tile",
        "--noparallel",
    )
    cases = [
        (
            "ordinary-common-band",
            polopt,
            [str(ROOT / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop")],
            "permutable-band",
            True,
            False,
        ),
        (
            "second-level-zero-row-band",
            polopt,
            [
                "--second-level-tile",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "symbolic-independent-2d.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "second-level-zero-row-band-iss",
            polopt,
            [
                "--second-level-tile",
                "--iss",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "symbolic-independent-2d.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "ordinary-phase-separated-mixed-depth",
            polopt,
            [
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "ordinary-phase-separated-mixed-depth-iss",
            polopt,
            [
                "--iss",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "mixed-depth-semantic-band",
            polopt,
            [
                "--identity-tiled",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "mixed-depth-semantic-band-iss",
            polopt,
            [
                "--identity-tiled",
                "--iss",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "second-level-mixed-depth-semantic-band",
            polopt,
            [
                "--second-level-tile",
                "--identity-tiled",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "second-level-mixed-depth-semantic-band-iss",
            polopt,
            [
                "--second-level-tile",
                "--identity-tiled",
                "--iss",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
            True,
            False,
        ),
        (
            "dependent-one-dimensional-band",
            polopt,
            [str(ROOT / "tools" / "parallel_current" / "fixtures" / "dependent.loop")],
            "permutable-band",
            True,
            False,
        ),
        (
            "frozen-diamond-phase-pair",
            polcert,
            [
                "--tiling",
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.midtransform.scop"),
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.posttile.scop"),
            ],
            "permutable-band",
            False,
            False,
        ),
        (
            "frozen-nonpermutable-band",
            polcert,
            [
                "--tiling",
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "nonpermutable-band.midtransform.scop"),
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "nonpermutable-band.posttile.scop"),
            ],
            "rejected",
            False,
            False,
        ),
    ]
    for suffix, target, expected in (
        ("preserved", "safe", "permutable-band"),
        ("delayed", "bad", "rejected"),
    ):
        cases.append((
            "outside-band-write-" + suffix,
            polcert,
            ["--tiling", "--second-level-tile",
             str(ROOT / "tools/tiling_routes/fixtures/program3-outside-band.midtransform.scop"),
             str(ROOT / f"tools/tiling_routes/fixtures/program3-outside-band.{target}-posttile.scop")],
            expected, False, False,
        ))
    for name, route_args in (
        ("explicit-ordinary-noloop", explicit_tile_flags),
        ("explicit-identity-noloop", (*explicit_tile_flags, "--identity")),
        ("explicit-diamond-noloop", ("--diamond-tile",)),
        ("explicit-second-level-noloop", ("--second-level-tile",)),
    ):
        for iss_suffix, iss_args in (("", ()), ("-iss", ("--iss",))):
            cases.append(
                (
                    f"{name}{iss_suffix}",
                    polopt,
                    [*route_args, *iss_args, str(noloop)],
                    "rejected",
                    False,
                    True,
                )
            )

    case_names = [case[0] for case in cases]
    duplicate_names = sorted(
        name for name in set(case_names) if case_names.count(name) > 1
    )
    missing_names = sorted(REQUIRED_CASE_NAMES.difference(case_names))
    if duplicate_names or missing_names:
        if duplicate_names:
            print(
                "[direct-route] duplicate required cases: "
                + ", ".join(duplicate_names)
            )
        if missing_names:
            print(
                "[direct-route] missing required cases: "
                + ", ".join(missing_names)
            )
        return 1

    failures: list[str] = []
    for (
        name,
        executable,
        command_args,
        expected_route,
        expect_optimized_output,
        expect_rejection_alarm,
    ) in cases:
        failure = run_case(
            executable,
            command_args,
            expected_route,
            args.timeout,
            expect_optimized_output=expect_optimized_output,
            expect_rejection_alarm=expect_rejection_alarm,
        )
        print(
            f"[direct-route] {'PASS' if failure is None else 'FAIL'} case={name} "
            f"expected=route:{expected_route},optimized-output:{str(expect_optimized_output).lower()},"
            f"rejection-alarm:{str(expect_rejection_alarm).lower()},fallbacks:0 "
            f"actual={'all-route-assertions-matched' if failure is None else 'route-assertion-mismatch'} "
            "interpretation="
            + (
                "direct-only-route-contract-matched"
                if failure is None
                else "route-output-or-alarm-did-not-match"
            )
        )
        if failure is not None:
            failures.append(f"{name}: {failure}")
    if failures:
        print("[direct-route] FAIL")
        print("\n".join(failures))
        return 1
    print(
        f"[direct-route] PASS expected={len(cases)},fallbacks:0 "
        f"actual={len(cases)},fallbacks:0 interpretation=all-direct-route-contracts-matched"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
