#!/usr/bin/env python3

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from pluto_versions import locate_buggy_pluto_and_polycc
from innerpar_semantics import checked_state, validate_checked_result


PLUTO_FLAGS = [
    "--notile",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--parallel",
]


def run(cmd, *, cwd=None, env=None, timeout=30):
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
    require(proc.returncode == 0, f"{label} failed with exit {proc.returncode}:\n{proc.stdout}")
    try:
        return int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(f"{label} returned non-integer output: {proc.stdout!r}") from exc


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture_dir = repo / "tests" / "pluto-bugs" / "vanished-outer-parallel"
    source = fixture_dir / "vanished_outer_parallel.c"
    loop = fixture_dir / "vanished_outer_parallel.loop"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists(), "missing vanished-loop fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-miscompile-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)

        pluto_proc = run([polycc, *PLUTO_FLAGS, work_source.name], cwd=work)
        generated = work / "vanished_outer_parallel.pluto.c"
        require(
            pluto_proc.returncode == 0,
            f"Pluto did not silently accept the reproducer:\n{pluto_proc.stdout}",
        )
        require(generated.exists(), "Pluto returned success without generated C output")
        generated_text = generated.read_text()
        require(
            re.search(r"#pragma omp parallel for[^\n]*\n\s*for \(", generated_text) is not None,
            "Pluto output did not contain an OpenMP parallel loop",
        )
        print(
            "[pluto-miscompile] producer: expected=success-with-inner-OpenMP "
            "actual=exit-0,omp-loop interpretation=unsafe-loop-substitution"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run(
            [compiler, "-O2", "-fopenmp", generated, "-o", optimized_exe]
        )
        require(
            optimized_build.returncode == 0,
            f"optimized build failed:\n{optimized_build.stdout}",
        )

        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        require(baseline == 10000, f"unexpected baseline result: {baseline}")
        omp_env = os.environ.copy()
        omp_env.update({"OMP_NUM_THREADS": "4", "OMP_DYNAMIC": "FALSE"})
        optimized = [
            parse_int_output("optimized execution", run([optimized_exe], env=omp_env))
            for _ in range(3)
        ]
        require(
            any(value != baseline for value in optimized),
            f"unsafe OpenMP executions unexpectedly matched the baseline: {optimized}",
        )
        print(
            f"[pluto-miscompile] execution: expected={baseline} "
            f"actual={','.join(map(str, optimized))} consistency=mismatch"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        reference = checked_state(loop.read_text(), work, 'loop-reference', compiler, run, fixture='vanished')
        require(reference[-1] == baseline, 'Loop reference disagrees with the C witness')

        strict = run(
            [polopt, *PLUTO_FLAGS[:-1], "--parallel", "--parallel-strict", loop],
            cwd=work,
            env=polcert_env,
        )
        outcome = validate_checked_result(strict, reference, work, 'strict-state', compiler, run,
                                          strict=True, fixture='vanished', require_tiling=False)
        print(
            "[pluto-miscompile] polcert-hint: expected=singleton-parallel "
            f"actual=exit-{strict.returncode},{outcome} "
            "interpretation=vanished-coordinate-did-not-transfer-inward"
        )

        actual_inner = run(
            [polopt, "--notile", "--parallel-current", "1", loop],
            cwd=work,
            env=polcert_env,
        )
        require(actual_inner.returncode != 0, "PolCert accepted Pluto's actual dependent t2 loop")
        require(
            "source=explicit-current reason=not-certifiable-or-out-of-range"
            in actual_inner.stdout,
            f"PolCert did not report rejection of current dimension 1:\n{actual_inner.stdout}",
        )
        print(
            f"[pluto-miscompile] polcert-inner-loop: expected=rejected "
            f"actual=exit-{actual_inner.returncode} interpretation=dependence-detected"
        )

    print("[pluto-miscompile] OK (white-box defect reproduced and rejected)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-miscompile] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
