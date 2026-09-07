#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "polopt-generated" / "tools"))
sys.path.insert(0, str(ROOT / "tools" / "diamond_tiling"))

import check_polopt_cases
import run_pluto_diamond_suite


class StrictCorpusTelemetryTests(unittest.TestCase):
    def check_stderr(self, stderr: str, expected: str) -> None:
        with tempfile.TemporaryDirectory(prefix="polcert-route-telemetry-") as tmp:
            case_dir = pathlib.Path(tmp) / "synthetic"
            case_dir.mkdir()
            (case_dir / "stderr.txt").write_text(stderr, encoding="utf-8")
            check_polopt_cases.check_tiling_validation(case_dir, expected)

    def test_direct_band_route_is_distinct(self) -> None:
        self.check_stderr(
            "[tiling-validation] route=permutable-band\n",
            "permutable-band",
        )

    def test_actual_schedule_route_is_distinct(self) -> None:
        self.check_stderr(
            "[tiling-validation] route=actual-schedule\n",
            "actual-schedule",
        )
        with self.assertRaises(SystemExit):
            self.check_stderr(
                "[tiling-validation] route=actual-schedule\n",
                "permutable-band",
            )

    def test_no_loop_is_the_only_not_applicable_status(self) -> None:
        self.check_stderr(
            "[tiling-validation] status=not-applicable reason=no-loop\n",
            "not-applicable:no-loop",
        )

    def test_extra_route_is_rejected(self) -> None:
        with self.assertRaises(SystemExit):
            self.check_stderr(
                "[tiling-validation] route=permutable-band\n"
                "[tiling-validation] route=rejected\n",
                "permutable-band",
            )

    def test_alarm_is_rejected(self) -> None:
        with self.assertRaises(SystemExit):
            self.check_stderr(
                "[tiling-validation] route=permutable-band\n"
                "[alarm] requested checked optimization was rejected\n",
                "permutable-band",
            )

    def test_fallback_marker_is_case_insensitively_rejected(self) -> None:
        with self.assertRaises(SystemExit):
            self.check_stderr(
                "[tiling-validation] route=permutable-band\n"
                "General-Fallback\n",
                "permutable-band",
            )


class DiamondPhaseTelemetryTests(unittest.TestCase):
    accepted = (
        "[PHASE] affine(before, mid): OK\n"
        "[PHASE] tiling(mid, posttile): OK route=permutable-band\n"
        "[PHASE] affine(posttile, after): OK\n"
        "[OK] Diamond phase-aligned validation succeeded\n"
    )
    rejected = (
        "[PHASE] affine(before, mid): OK\n"
        "[PHASE] tiling(mid, posttile): FAIL route=rejected\n"
        "[PHASE] affine(posttile, after): OK\n"
        "[FAIL] Diamond phase-aligned validation failed\n"
    )

    def test_exact_direct_phase_route_is_accepted(self) -> None:
        self.assertTrue(
            run_pluto_diamond_suite.phase_validation_succeeds(
                self.accepted,
                "permutable-band",
            )
        )

    def test_exact_rejected_phase_route_is_accepted(self) -> None:
        self.assertTrue(
            run_pluto_diamond_suite.phase_validation_rejects_tiling(
                self.rejected,
            )
        )

    def test_extra_phase_route_is_rejected(self) -> None:
        self.assertFalse(
            run_pluto_diamond_suite.phase_validation_succeeds(
                self.accepted
                + "[PHASE] tiling(mid, posttile): OK route=general-fallback\n",
                "permutable-band",
            )
        )

    def test_fallback_marker_outside_route_is_rejected(self) -> None:
        self.assertFalse(
            run_pluto_diamond_suite.phase_validation_succeeds(
                self.accepted + "fallback selected\n",
                "permutable-band",
            )
        )


if __name__ == "__main__":
    unittest.main()
