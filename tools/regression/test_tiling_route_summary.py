#!/usr/bin/env python3
from __future__ import annotations

import tempfile
from pathlib import Path

from run_regression_suite import CheckResult, build_tiling_route_summary


def make_result(root: Path, name: str, stdout: str) -> CheckResult:
    stdout_path = root / f"{name}.stdout.txt"
    stderr_path = root / f"{name}.stderr.txt"
    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text("", encoding="utf-8")
    return CheckResult(
        name=name,
        command=[name],
        returncode=0,
        elapsed_seconds=0.0,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def make_results(root: Path, direct_actual: int) -> list[CheckResult]:
    return [
        make_result(
            root,
            "direct-only-tiling-route-smoke",
            "[direct-route] PASS expected=20,fallbacks:0 "
            f"actual={direct_actual},fallbacks:0 "
            "interpretation=all-direct-route-contracts-matched\n",
        ),
        make_result(root, "scalar-interleaved-tiling-route", "PASS\n"),
        make_result(
            root,
            "non-second-level-tiling-routes",
            "[non-second-level-routes] PASS "
            "expected=permutable-band:84,fallbacks:0,vector-rejections:6 "
            "actual=permutable-band:84,fallbacks:0,vector-rejections:6 "
            "interpretation=all-one-level-route-contracts-matched\n",
        ),
        make_result(root, "second-level-suite", "PASS\n"),
        make_result(root, "pluto-compat-suite", "PASS\n"),
        make_result(
            root,
            "strict-loop-suite",
            "tiling_validation_permutable_band=61\n"
            "tiling_validation_not_applicable_no_loop=1\n"
            "tiling_validation_fallback=0\n",
        ),
    ]


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="tiling-route-summary-unit-") as tmp:
        root = Path(tmp)
        valid = build_tiling_route_summary(make_results(root, direct_actual=20))
        assert valid["verified"] is True
        assert valid["zero_tiling_validation_fallbacks"] is True
        assert valid["direct_route_smoke"] == {
            "cases": 20,
            "zero_fallbacks": True,
        }
        assert valid["non_second_level"] == {
            "cases": 90,
            "permutable_band": 84,
            "validation_fallback": 0,
            "explicit_vector_rejection": 6,
        }
        assert valid["strict_loop_corpus"]["verified"] is True

        mismatched = build_tiling_route_summary(
            make_results(root, direct_actual=19)
        )
        assert mismatched["verified"] is False
        assert mismatched["zero_tiling_validation_fallbacks"] is False
        assert mismatched["direct_route_smoke"] == {
            "cases": None,
            "zero_fallbacks": False,
        }

    print(
        "[tiling-route-summary-unit] PASS "
        "expected=matching-counts-accepted,mismatched-counts-rejected "
        "actual=matching-counts-accepted,mismatched-counts-rejected "
        "interpretation=regression-summary-parses-readable-route-logs-fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
