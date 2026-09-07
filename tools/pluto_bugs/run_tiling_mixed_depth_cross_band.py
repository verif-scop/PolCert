#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from pluto_versions import locate_buggy_pluto_and_polycc


PLUTO_FLAGS = [
    "--maxfuse",
    "--noparallel",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--nounrolljam",
    "--rar",
]


def run(cmd, *, cwd=None, env=None, timeout=120):
    return subprocess.run(
        [str(arg) for arg in cmd],
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout,
        check=False,
    )


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def parse_int_output(label, proc):
    require(
        proc.returncode == 0,
        f"{label} failed with exit {proc.returncode}:\n{proc.stdout}",
    )
    try:
        return int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(
            f"{label} returned non-integer output: {proc.stdout!r}"
        ) from exc


def build_and_run(compiler, source, output):
    build = run([compiler, "-std=c11", "-O2", source, "-o", output])
    require(build.returncode == 0, f"build failed for {source}:\n{build.stdout}")
    return parse_int_output(str(output), run([output]))


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture = repo / "tests" / "pluto-bugs" / "tiling-mixed-depth-cross-band"
    source = fixture / "tiling_mixed_depth_cross_band.c"
    loop = fixture / "tiling_mixed_depth_cross_band.loop"
    tile_sizes = fixture / "tile.sizes"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "cc")

    require(polopt.is_file(), f"missing PolCert executable: {polopt}")
    require(
        source.is_file() and loop.is_file() and tile_sizes.is_file(),
        "missing mixed-depth tiling fixtures",
    )

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-mixed-depth-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(tile_sizes, work / "tile.sizes")

        affine_source = work / "affine.c"
        tiled_source = work / "tiled.c"
        affine = run(
            [polycc, work_source.name, *PLUTO_FLAGS, "--notile", "-o", affine_source.name],
            cwd=work,
        )
        tiled = run(
            [polycc, work_source.name, *PLUTO_FLAGS, "--tile", "-o", tiled_source.name],
            cwd=work,
        )
        require(
            affine.returncode == 0 and affine_source.is_file(),
            f"Pluto affine-only route failed:\n{affine.stdout}",
        )
        require(
            tiled.returncode == 0 and tiled_source.is_file(),
            f"Pluto tiled route failed:\n{tiled.stdout}",
        )

        baseline_value = build_and_run(compiler, work_source, work / "baseline")
        affine_value = build_and_run(compiler, affine_source, work / "affine")
        tiled_value = build_and_run(compiler, tiled_source, work / "tiled")
        require(baseline_value == 42, f"unexpected source result: {baseline_value}")
        require(
            affine_value == baseline_value,
            f"affine schedule already changed the result: {affine_value}",
        )
        require(
            tiled_value == 6 and tiled_value != baseline_value,
            f"tiled output did not reproduce the wrong result: {tiled_value}",
        )
        print(
            "[pluto-tiling-mixed-depth] execution: "
            f"expected={baseline_value} affine={affine_value} actual={tiled_value} "
            "consistency=mismatch interpretation=tiling-reversed-cross-band-dependence"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked = run(
            [
                polopt,
                "--pluto-compat",
                *PLUTO_FLAGS,
                "--tile",
                "--tile-sizes-file",
                tile_sizes,
                loop,
            ],
            cwd=repo,
            env=polcert_env,
        )
        require(
            checked.returncode == 2
            and "[tiling-validation] route=rejected" in checked.stdout
            and "[alarm] requested checked optimization was rejected" in checked.stdout,
            "PolCert did not reject the illegal tiled candidate:\n" + checked.stdout,
        )
        require(
            "== Optimized Loop ==" not in checked.stdout,
            "rejected route emitted an optimized loop",
        )
        print(
            "[pluto-tiling-mixed-depth] checked-pipeline: "
            "expected=reject-illegal-tiling actual=rejected-no-output "
            "interpretation=formal-tiling-boundary-failed-closed"
        )

    print("[pluto-tiling-mixed-depth] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-tiling-mixed-depth] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
