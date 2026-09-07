#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.regression.explore_unrolljam_effect_corpus import (
    tiling_validation_route_absent,
)


class TilingRouteGuardTest(unittest.TestCase):
    def test_checks_complete_stderr_not_only_tail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            stderr_path = Path(tmp) / "polopt.stderr.txt"
            stderr_path.write_text(
                "[tiling-validation] route=rejected\n" + ("x" * 2400),
                encoding="utf-8",
            )
            self.assertFalse(tiling_validation_route_absent(str(stderr_path)))

    def test_accepts_stderr_without_tiling_route(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            stderr_path = Path(tmp) / "polopt.stderr.txt"
            stderr_path.write_text("x" * 2400, encoding="utf-8")
            self.assertTrue(tiling_validation_route_absent(str(stderr_path)))

    def test_missing_stderr_fails_closed(self) -> None:
        self.assertFalse(tiling_validation_route_absent("/missing/polopt.stderr.txt"))


if __name__ == "__main__":
    unittest.main()
