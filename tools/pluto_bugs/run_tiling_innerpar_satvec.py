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
    "--identity",
    "--tile",
    "--parallel",
    "--innerpar",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
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
    fixture_dir = repo / "tests" / "pluto-bugs" / "tiling-innerpar-satvec"
    source = fixture_dir / "tiling_innerpar_satvec.c"
    loop = fixture_dir / "tiling_innerpar_satvec.loop"
    tile_sizes = fixture_dir / "tile.sizes"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists() and tile_sizes.exists(), "missing innerpar bug fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-innerpar-bug-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(tile_sizes, work / "tile.sizes")

        pluto_proc = run([polycc, "--dumpscop", *PLUTO_FLAGS, work_source.name], cwd=work)
        stem = source.stem
        generated = work / f"{stem}.pluto.c"
        require(pluto_proc.returncode == 0, f"Pluto rejected the reproducer:\n{pluto_proc.stdout}")
        require(generated.exists(), "Pluto omitted the generated C artifact")
        generated_text = generated.read_text()
        require(
            re.search(
                r"#pragma omp parallel for[^\n]*\n\s*for \(",
                generated_text,
            )
            is not None,
            "Pluto output did not contain an OpenMP parallel loop",
        )
        print(
            "[pluto-tiling-bug] producer: expected=OpenMP-candidate "
            "actual=exit-0,omp-loop interpretation=stale-satisfaction-metadata"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run([compiler, "-O2", "-fopenmp", generated, "-o", optimized_exe])
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")
        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        omp_env = os.environ.copy()
        omp_env.update({"OMP_NUM_THREADS": "4", "OMP_DYNAMIC": "FALSE"})
        optimized = [
            parse_int_output("optimized execution", run([optimized_exe], env=omp_env))
            for _ in range(5)
        ]
        require(baseline == 310235039, f"unexpected baseline result: {baseline}")
        require(any(value != baseline for value in optimized), f"unsafe executions matched baseline: {optimized}")
        print(
            f"[pluto-tiling-bug] execution: expected={baseline} "
            f"actual={','.join(map(str, optimized))} consistency=mismatch"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        reference = checked_state(loop.read_text(), work, 'loop-reference', compiler, run)
        require(reference[-1] == baseline, 'Loop reference disagrees with the C witness')
        checked = run([polopt, *PLUTO_FLAGS, loop], cwd=work, env=polcert_env)
        outcome = validate_checked_result(checked, reference, work, 'checked-state', compiler, run)
        print(
            "[pluto-tiling-bug] checked-pipeline: "
            "expected=tiling-accepted,no-nontrivial-parallel-loop "
            f"actual=exit-0,permutable-band,{outcome} "
            "interpretation=complete-state-and-singleton-check"
        )

        strict = run([polopt, *PLUTO_FLAGS, "--parallel-strict", loop], cwd=work, env=polcert_env)
        strict_outcome = validate_checked_result(strict, reference, work, 'strict-state', compiler, run, strict=True)
        print(
            "[pluto-tiling-bug] strict-pipeline: "
            "expected=rejection-or-state-equivalent-singleton "
            f"actual=exit-{strict.returncode},{strict_outcome} "
            "interpretation=actual-hint-checked"
        )

        # Separate from the unmodified historical producer replay: force a
        # witnessed unsafe hint, leaving the producer's relations untouched.
        wrapper = work / 'witnessed-unsafe-hint.py'
        shutil.copy2(Path(__file__).with_name('innerpar_unsafe_hint.py'), wrapper)
        wrapper.chmod(0o755)
        witness = work / 'unsafe-hint-witness.json'
        witness_env = polcert_env.copy()
        witness_env.update(POLCERT_PLUTO=str(wrapper),
                           POLCERT_INNERPAR_REAL_PLUTO=str(pluto),
                           POLCERT_INNERPAR_HINT_WITNESS=str(witness))
        unsafe_hint = run([polopt, *PLUTO_FLAGS, '--parallel-strict', loop],
                          cwd=work, env=witness_env)
        require(witness.exists(), 'unsafe hint wrapper did not establish an in-domain dependence witness')
        require(unsafe_hint.returncode != 0
                and 'status=rejected source=pluto-hint reason=no-certifiable-dimension' in unsafe_hint.stdout
                and '== Optimized Loop ==' not in unsafe_hint.stdout,
                'strict route accepted the witnessed dependence-carrying hint:\n' + unsafe_hint.stdout)
        print('[pluto-tiling-bug] witnessed-unsafe-hint: expected=strict-rejection '
              'actual=rejected,no-output interpretation=in-domain-dependence-detected')

        unsafe_tile_loop = run(
            [polopt, "--identity-tiled", "--parallel-current", "2", loop],
            cwd=work,
            env=polcert_env,
        )
        require(
            unsafe_tile_loop.returncode != 0
            and (
                "source=explicit-current reason=not-certifiable-or-out-of-range"
                in unsafe_tile_loop.stdout
            )
            and "== Optimized Loop ==" not in unsafe_tile_loop.stdout,
            "PolCert accepted the dependence-carrying tile-loop coordinate:\n"
            f"{unsafe_tile_loop.stdout}",
        )
        print(
            "[pluto-tiling-bug] dependent-tile-loop: "
            f"expected=rejected actual=exit-{unsafe_tile_loop.returncode} "
            "interpretation=dependence-detected"
        )

    print("[pluto-tiling-bug] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-tiling-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
