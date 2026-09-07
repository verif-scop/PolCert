#!/usr/bin/env python3
"""Require direct-band acceptance of the nine scalar/phase two-level regressions."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


CASES = ("corcol3", "dct", "fusion5", "gemver", "matmul-seq", "mxv-seq",
         "mxv-seq3", "pca", "tce")
FLAGS = ("--pluto-compat", "--tile", "--second-level-tile", "--smartfuse",
         "--nointratileopt", "--noprevector", "--nounrolljam",
         "--nodiamond-tile", "--noparallel")
ROUTE = re.compile(r"\[tiling-validation\] route=([a-z-]+)")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def accepted_direct(returncode: int, stdout: str, stderr: str) -> bool:
    return (returncode == 0 and ROUTE.findall(stdout + stderr) == ["permutable-band"]
            and "== Optimized Loop ==" in stdout and "[alarm]" not in stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--polopt", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", choices=CASES, nargs="+", default=list(CASES))
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    root = args.source_root.resolve()
    binary = (args.polopt or root / "polopt").resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, COMPCERT_CONFIG=str(root / "tests/pluto/polcert.ini"))
    records = []
    for name in args.cases:
        source = root / "tests/polopt-generated/inputs" / (name + ".loop")
        command = [str(binary), *FLAGS, str(source)]
        start = time.monotonic()
        try:
            result = subprocess.run(command, cwd=root, env=env, capture_output=True,
                                    text=True, timeout=args.timeout)
            code, stdout, stderr = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as error:
            code = -1
            stdout = (error.stdout or b"").decode(errors="replace")
            stderr = (error.stderr or b"").decode(errors="replace") + "\nTEST TIMEOUT\n"
        row = dict(case=name, command=command, cwd=str(root), source_sha256=sha(source),
                   returncode=code, elapsed_s=time.monotonic() - start,
                   routes=ROUTE.findall(stdout + stderr),
                   direct_accepted=accepted_direct(code, stdout, stderr))
        (out / (name + ".stdout.txt")).write_text(stdout)
        (out / (name + ".stderr.txt")).write_text(stderr)
        records.append(row)
        (out / "results.json").write_text(json.dumps(dict(binary=str(binary),
            binary_sha256=sha(binary), collector_sha256=sha(Path(__file__)),
            expected_cases=list(args.cases), records=records), indent=2) + "\n")
        print(f"{name}: routes={row['routes']} direct={row['direct_accepted']}", flush=True)
    return 0 if all(row["direct_accepted"] for row in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
