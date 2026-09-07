#!/usr/bin/env python3
from __future__ import annotations

import os
import subprocess
from pathlib import Path


DEFAULT_BUGGY_ROOT = Path("/opt/polcert/pluto-buggy")
BASELINE_ENV = Path(__file__).resolve().parents[1] / "ci" / "pluto-baseline.env"


def baseline_value(name: str) -> str | None:
    if not BASELINE_ENV.is_file():
        return None
    prefix = f"{name}="
    for line in BASELINE_ENV.read_text().splitlines():
        if line.startswith(prefix):
            value = line[len(prefix) :].strip()
            return value.strip("'\"") or None
    return None


def locate_buggy_pluto_and_polycc() -> tuple[Path, Path]:
    configured_pluto = os.environ.get("POLCERT_BUGGY_PLUTO")
    configured_polycc = os.environ.get("POLCERT_BUGGY_POLYCC")

    pluto = (
        Path(configured_pluto).resolve()
        if configured_pluto
        else DEFAULT_BUGGY_ROOT / "tool" / "pluto"
    )
    polycc = (
        Path(configured_polycc).resolve()
        if configured_polycc
        else pluto.parent.parent / "polycc"
    )

    if not pluto.is_file():
        raise AssertionError(
            "cannot locate the pinned buggy Pluto binary; "
            "set POLCERT_BUGGY_PLUTO or use the development image"
        )
    if not polycc.is_file():
        raise AssertionError(
            "cannot locate the pinned buggy polycc binary; "
            "set POLCERT_BUGGY_POLYCC or use the development image"
        )
    root = pluto.parent.parent
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        text=True,
        capture_output=True,
        check=False,
    )
    if head.returncode != 0:
        raise AssertionError(f"cannot identify buggy Pluto checkout at {root}")
    actual_commit = head.stdout.strip()
    expected_commit = os.environ.get(
        "POLCERT_BUGGY_PLUTO_GIT_COMMIT"
    ) or baseline_value("PLUTO_BUGGY_GIT_COMMIT")
    if not expected_commit:
        raise AssertionError(
            "cannot determine the required buggy Pluto revision from the "
            "environment or tools/ci/pluto-baseline.env"
        )
    if actual_commit != expected_commit:
        raise AssertionError(
            "buggy Pluto revision mismatch: "
            f"expected {expected_commit}, actual {actual_commit}"
        )
    version = subprocess.run(
        [str(pluto), "--version"],
        text=True,
        capture_output=True,
        check=False,
    )
    version_line = (version.stdout + version.stderr).splitlines()
    version_text = version_line[0] if version_line else ""
    # Pluto prints its version and exits nonzero, so the revision marker is the
    # stable contract; the process status is not.
    if expected_commit[:7] not in version_text:
        raise AssertionError(
            "buggy Pluto binary revision mismatch: "
            f"expected marker {expected_commit[:7]}, actual {version_text!r}"
        )
    print(
        "[pluto-baseline] role=bug-reproducer "
        f"commit={actual_commit} root={root}"
    )
    return pluto, polycc
