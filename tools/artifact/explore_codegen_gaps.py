#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
PLUTO = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
MATMUL = ROOT / "tests" / "polopt-generated" / "inputs" / "matmul.loop"


def run(cmd: list[str], *, cwd: Path = ROOT, timeout: int = 30) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def export_scop(out_dir: Path) -> Path:
    proc = run([str(POLOPT), "--dump-extracted-openscop", "--extract-only", str(MATMUL)])
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    scop = out_dir / "matmul.scop"
    scop.write_text(proc.stdout)
    return scop


def run_pluto_codegen(scop: Path, out_dir: Path, mode: str, unrolljam: bool) -> dict[str, object]:
    run_dir = out_dir / mode
    run_dir.mkdir(parents=True, exist_ok=True)
    local_scop = run_dir / scop.name
    shutil.copyfile(scop, local_scop)
    flags = [
        "--dumpscop",
        "--readscop",
        "--tile",
        "--smartfuse",
        "--nointratileopt",
        "--noprevector",
        "--nodiamond-tile",
        "--noparallel",
    ]
    if unrolljam:
        flags.extend(["--unrolljam", "--ufactor=4"])
    else:
        flags.append("--nounrolljam")
    proc = run([str(PLUTO), *flags, local_scop.name], cwd=run_dir)
    c_path = Path(str(local_scop) + ".pluto.c")
    after_path = Path(str(local_scop) + ".afterscheduling.scop")
    return {
        "mode": mode,
        "exit": proc.returncode,
        "stdout": proc.stdout[-1000:],
        "stderr": proc.stderr[-1000:],
        "c_path": str(c_path),
        "after_path": str(after_path),
        "c_text": c_path.read_text() if c_path.exists() else "",
        "after_text": after_path.read_text() if after_path.exists() else "",
    }


def run_polopt_checked_unroll() -> dict[str, object]:
    proc = run(
        [
            str(POLOPT),
            "--pluto-compat",
            "--explain",
            "--tile",
            "--smartfuse",
            "--nointratileopt",
            "--noprevector",
            "--unrolljam",
            "--ufactor=4",
            "--nodiamond-tile",
            "--noparallel",
            str(MATMUL),
        ]
    )
    stdout = proc.stdout
    return {
        "exit": proc.returncode,
        "stdout": proc.stdout[-1000:],
        "stderr": proc.stderr[-1000:],
        "accepted": proc.returncode == 0,
        "checked_factor_note_present": "checked post flags: --ufactor=4" in stdout,
        "block_offset_marker_present": "(4 * i" in stdout and "+ 3)" in stdout,
        "checked_remainder_loop_marker_present": "for i" in stdout and " / 4)" in stdout,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-root", type=Path, default=Path("/tmp/polcert-codegen-gaps"))
    args = ap.parse_args()
    out_dir = args.output_root.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    scop = export_scop(out_dir)
    nounroll = run_pluto_codegen(scop, out_dir, "nounrolljam", False)
    unroll = run_pluto_codegen(scop, out_dir, "unrolljam", True)
    after_same = nounroll["after_text"] == unroll["after_text"]
    code_differs = nounroll["c_text"] != unroll["c_text"]
    unroll_has_factor = "+=4" in str(unroll["c_text"])
    unroll_has_remainder = "for (;t4<=" in str(unroll["c_text"]) or "for (; t4<=" in str(unroll["c_text"])
    polopt_unroll = run_polopt_checked_unroll()

    result = {
        "mode": "pluto-codegen-gap-unrolljam",
        "fixture": str(MATMUL.relative_to(ROOT)),
        "pluto_unrolljam_exit": unroll["exit"],
        "pluto_nounrolljam_exit": nounroll["exit"],
        "after_scheduling_scops_equal": after_same,
        "generated_c_differs": code_differs,
        "unroll_factor_marker_present": unroll_has_factor,
        "remainder_loop_marker_present": unroll_has_remainder,
        "polopt_checked_unrolljam": polopt_unroll,
        "output_root": str(out_dir),
    }
    print(json.dumps(result, indent=2, sort_keys=True))

    ok = (
        nounroll["exit"] == 0
        and unroll["exit"] == 0
        and after_same
        and code_differs
        and unroll_has_factor
        and unroll_has_remainder
        and bool(polopt_unroll["accepted"])
        and bool(polopt_unroll["checked_factor_note_present"])
        and bool(polopt_unroll["block_offset_marker_present"])
        and bool(polopt_unroll["checked_remainder_loop_marker_present"])
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
