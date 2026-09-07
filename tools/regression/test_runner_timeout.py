#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

from run_regression_suite import run_check


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        result = run_check(
            "timeout-probe",
            [
                sys.executable,
                "-c",
                (
                    "import sys, time; "
                    "print('partial stdout', flush=True); "
                    "print('partial stderr', file=sys.stderr, flush=True); "
                    "time.sleep(2)"
                ),
            ],
            Path(tmp),
            1,
        )
        assert result.returncode == 124
        assert "partial stdout" in Path(result.stdout_path).read_text()
        stderr = Path(result.stderr_path).read_text()
        assert "partial stderr" in stderr
        assert "[check-smoke] timeout after 1 seconds" in stderr
    print("[regression-runner-timeout-unit] PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
