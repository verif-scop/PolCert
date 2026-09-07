#!/usr/bin/env python3
"""Replace Pluto phase outputs with a valid nonpermutable tiling pair."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    args = sys.argv[1:]
    real_pluto = os.environ.get("POLCERT_REAL_PLUTO", "/pluto/tool/pluto")
    proc = subprocess.run([real_pluto, *args], check=False)
    if proc.returncode != 0:
        return proc.returncode

    inputs = [Path(arg).resolve() for arg in args if arg.endswith(".scop")]
    if not inputs:
        return 70

    source = inputs[-1]
    fixtures = Path(__file__).resolve().parent / "fixtures"
    if "--tile" in args:
        # A single invocation exports both checked phases.  Keep its final
        # alias identical to posttile, so rejection tests reach the tiling
        # checker rather than the driver's phase-consistency guard.
        phases = (
            ("affine", "midtransform", ("midtransform",)),
            ("tiled", "posttile", ("posttile", "afterscheduling")),
        )
    else:
        phases = (("affine", "midtransform", ("afterscheduling",)),)
    for phase, fixture_phase, output_phases in phases:
        replacement = fixtures / f"nonpermutable-band.{fixture_phase}.scop"
        outputs = [source.with_name(source.name + f".{name}.scop")
                   for name in output_phases]
        if any(not output.is_file() for output in outputs):
            print("[frozen-nonpermutable-pluto] missing phase output", file=sys.stderr)
            return 71
        for output in outputs:
            shutil.copyfile(replacement, output)
        print(
            f"[frozen-nonpermutable-pluto] phase={phase} "
            f"replaced {','.join(output.name for output in outputs)} "
            f"with {replacement.name}",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
