#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import tempfile
import unittest
from unittest import mock

import proof_report


class ProofReportTests(unittest.TestCase):
    def build(self, coq: str, extracted: str = "") -> dict[str, object]:
        with tempfile.TemporaryDirectory(prefix="polcert-proof-report-") as tmp:
            root = pathlib.Path(tmp)
            source_dir = root / "src"
            extraction_dir = root / "extraction"
            source_dir.mkdir()
            extraction_dir.mkdir()
            (source_dir / "Fixture.v").write_text(coq, encoding="utf-8")
            if extracted:
                (extraction_dir / "Fixture.ml").write_text(extracted, encoding="utf-8")
            with mock.patch.object(
                proof_report, "ROOT", root
            ), mock.patch.object(
                proof_report, "SCAN_DIRS", ["src"]
            ), mock.patch.object(
                proof_report, "TOP_LEVEL_ROUTES", []
            ):
                return proof_report.build_report()

    def test_clean_report_passes(self) -> None:
        report = self.build("Goal True. exact I. Qed.\n")
        self.assertFalse(proof_report.report_has_errors(report))

    def test_open_proofs_fail_but_comments_do_not(self) -> None:
        report = self.build(
            "(* Admitted. *)\nGoal True. Admitted.\nGoal True. Abort.\n"
        )
        self.assertEqual(report["admitted_count"], 1)
        self.assertEqual(report["abort_count"], 1)
        self.assertTrue(proof_report.report_has_errors(report))

    def test_unrealized_extraction_axiom_fails(self) -> None:
        report = self.build(
            "Goal True. exact I. Qed.\n",
            "(* AXIOM TO BE REALIZED *)\n",
        )
        self.assertEqual(report["extraction_axiom_count"], 1)
        self.assertTrue(proof_report.report_has_errors(report))

    def test_missing_listed_route_theorem_fails(self) -> None:
        with tempfile.TemporaryDirectory(prefix="polcert-proof-report-route-") as tmp:
            root = pathlib.Path(tmp)
            source_dir = root / "src"
            source_dir.mkdir()
            (source_dir / "Fixture.v").write_text(
                "Theorem present : True. exact I. Qed.\n", encoding="utf-8"
            )
            routes = [
                {
                    "route": "fixture",
                    "cli": "fixture",
                    "theorem_file": "src/Fixture.v",
                    "theorem_names": ["missing"],
                }
            ]
            with mock.patch.object(
                proof_report, "ROOT", root
            ), mock.patch.object(
                proof_report, "SCAN_DIRS", ["src"]
            ), mock.patch.object(
                proof_report, "TOP_LEVEL_ROUTES", routes
            ):
                report = proof_report.build_report()
        self.assertEqual(report["missing_route_theorem_count"], 1)
        self.assertTrue(proof_report.report_has_errors(report))


if __name__ == "__main__":
    unittest.main()
