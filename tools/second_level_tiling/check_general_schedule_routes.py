#!/usr/bin/env python3
"""Regression checks for witnessed tilings outside the specialized band routes.

These are full compiler runs, not a reinterpretation of a failed band check.
The negative case preserves tiling domains and access relations but reverses
the proposed tiled execution order of a dependent matrix multiplication.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


CASES = ("corcol3", "gemver", "dct", "mxv-seq3", "pca", "fusion5",
         "matmul-seq", "mxv-seq", "tce")
FLAGS = ("--pluto-compat", "--tile", "--second-level-tile", "--smartfuse",
         "--nointratileopt", "--noprevector", "--nounrolljam",
         "--nodiamond-tile", "--noparallel")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], env: dict[str, str], root: Path, timeout: int):
    started = time.perf_counter()
    proc = subprocess.Popen(command, cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    return proc.returncode, stdout, stderr, time.perf_counter() - started, timed_out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--polopt", type=Path, default=Path("./polopt"))
    parser.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--cases", nargs="*", choices=CASES, default=list(CASES))
    parser.add_argument("--skip-negative", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    polopt, pluto = args.polopt.resolve(), args.pluto.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, POLCERT_PLUTO=str(pluto),
               COMPCERT_CONFIG=str(root / "tests/pluto/polcert.ini"))
    rows = []
    cases = [(name, name, True) for name in args.cases]
    if not args.skip_negative:
        cases.append(("reversed-tiled-matmul", "matmul", False))
    for name, kernel, positive in cases:
        source = root / "tests/polopt-generated/inputs" / (kernel + ".loop")
        case_env = dict(env)
        if not positive:
            case_env.update(POLCERT_REAL_PLUTO=str(pluto),
                POLCERT_PLUTO=str(root / "tools/second_level_tiling/rejecting_pluto.py"),
                POLCERT_REJECTING_PLUTO_MODE="tiling-schedule")
        command = [str(polopt), *FLAGS, str(source)]
        code, stdout, stderr, seconds, timed_out = run(command, case_env, root, args.timeout)
        (output / (name + ".stdout.txt")).write_text(stdout)
        (output / (name + ".stderr.txt")).write_text(stderr)
        routes = [line.strip() for line in stderr.splitlines()
                  if line.startswith("[tiling-validation] route=")]
        if positive:
            passed = (code == 0 and routes == ["[tiling-validation] route=actual-schedule"]
                      and "== Optimized Loop ==" in stdout and "[alarm]" not in stderr)
        else:
            passed = (code != 0 and not timed_out
                      and routes == ["[tiling-validation] route=rejected"]
                      and "tiled scattering input coefficients" in stderr
                      and "== Optimized Loop ==" not in stdout)
        row = dict(case=name, expected="accept" if positive else "reject",
                   passed=passed, returncode=code, timed_out=timed_out,
                   routes=routes, wall_seconds=seconds, command=command,
                   source_sha256=sha(source))
        rows.append(row)
        (output / (name + ".json")).write_text(json.dumps(row, indent=2) + "\n")
        print(json.dumps(row), flush=True)
    report = dict(polopt_sha256=sha(polopt), pluto_sha256=sha(pluto),
                  config_sha256=sha(root / "tests/pluto/polcert.ini"),
                  script_sha256=sha(Path(__file__)), rows=rows,
                  all_passed=all(row["passed"] for row in rows))
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
