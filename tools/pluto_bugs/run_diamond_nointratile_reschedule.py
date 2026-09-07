#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from diamond_semantics import check_array_states


PLUTO_FLAGS = [
    "--tile",
    "--diamond-tile",
    "--nointratileopt",
    "--noparallel",
    "--noprevector",
    "--nounrolljam",
]

POLCERT_FLAGS = [
    "--pluto-compat",
    "--tile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--diamond-tile",
    "--noparallel",
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


def locate_pluto():
    configured = os.environ.get("POLCERT_PLUTO")
    if configured:
        pluto = Path(configured).resolve()
    elif Path("/pluto/tool/pluto").exists():
        pluto = Path("/pluto/tool/pluto")
    else:
        found = shutil.which("pluto")
        if found is None:
            raise AssertionError("cannot locate Pluto; set POLCERT_PLUTO")
        pluto = Path(found).resolve()

    configured_polycc = os.environ.get("POLCERT_POLYCC")
    if configured_polycc:
        polycc = Path(configured_polycc).resolve()
    elif pluto.parent.name == "tool" and (pluto.parent.parent / "polycc").exists():
        polycc = pluto.parent.parent / "polycc"
    else:
        found = shutil.which("polycc")
        if found is None:
            raise AssertionError("cannot locate polycc; set POLCERT_POLYCC")
        polycc = Path(found).resolve()
    return pluto, polycc


def parse_int_output(label, proc):
    require(proc.returncode == 0, f"{label} failed with exit {proc.returncode}:\n{proc.stdout}")
    try:
        return int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(f"{label} returned non-integer output: {proc.stdout!r}") from exc


def read_relations(path):
    """Read the explicit relations needed to witness this fixed fixture's RAW edge."""
    statements = []
    lines = iter(path.read_text().splitlines())
    for line in lines:
        kind = line.strip()
        if kind not in ("DOMAIN", "SCATTERING", "READ", "WRITE"):
            continue
        header = list(map(int, next(lines).split()))
        rows = []
        while len(rows) < header[0]:
            row = next(lines).split("#", 1)[0].strip()
            if row:
                rows.append(list(map(int, row.split())))
        if kind == "DOMAIN":
            statements.append({})
        statements[-1].setdefault(kind, []).append((header, rows))
    return statements


def relation_output(relation, point):
    header, rows = relation
    outputs = [None] * header[2]
    require(header[3] == len(point) and header[4:6] == [0, 0],
            "unexpected local or parameter dimensions in fixed fixture")
    for row in rows:
        coefficients = row[1:1 + len(outputs)]
        nonzero = [i for i, value in enumerate(coefficients) if value]
        require(row[0] == 0 and len(nonzero) == 1
                and abs(coefficients[nonzero[0]]) == 1,
                "expected explicit affine relation")
        index = nonzero[0]
        outputs[index] = -(sum(a * b for a, b in zip(
            row[1 + len(outputs):-1], point)) + row[-1]) // coefficients[index]
    require(None not in outputs, "incomplete explicit affine relation")
    return tuple(outputs)


def require_preserved_raw_edge(midpoint, posttile):
    schedules = []
    for path in (midpoint, posttile):
        statements = read_relations(path)
        require(len(statements) == 4, "diamond fixture statement count changed")
        pair = [statements[0], statements[3]]
        points = [(0,) * statement['DOMAIN'][0][0][2] for statement in pair]
        for statement, point in zip(pair, points):
            header, rows = statement["DOMAIN"][0]
            require(header[2] == len(point) and header[3:6] == [0, 0, 0],
                    "unexpected fixed fixture domain dimensions")
            require(all((row[-1] >= 0 if row[0] else row[-1] == 0)
                        for row in rows), "zero instance no longer belongs to domain")
        writes = {relation_output(rel, points[0]) for rel in pair[0]["WRITE"]}
        reads = {relation_output(rel, points[1]) for rel in pair[1]["READ"]}
        require((1, 0, 0) in writes & reads, "missing S1 -> S4 RAW edge on ey[0][0]")
        schedules.append(tuple(relation_output(s["SCATTERING"][0], p)
                               for s, p in zip(pair, points)))
    require(schedules[0][0] < schedules[0][1]
            and schedules[1][0] < schedules[1][1],
            f"RAW order is not preserved at the tiling boundary: {schedules}")
    print(f"[pluto-diamond-nointra] intermediate-RAW: S1={schedules[1][0]} "
          f"S4={schedules[1][1]} location=ey[0][0] interpretation=order-preserved")


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture = repo / "tests" / "pluto-bugs" / "diamond-nointratile-reschedule"
    source = fixture / "diamond_nointratile.c"
    tile_sizes = fixture / "tile.sizes"
    polopt = repo / "polopt"
    pluto, polycc = locate_pluto()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and tile_sizes.exists(), "missing diamond regression fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-diamond-nointra-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(tile_sizes, work / "tile.sizes")

        producer = run([polycc, *PLUTO_FLAGS, work_source.name], cwd=work)
        generated = work / f"{source.stem}.pluto.c"
        require(producer.returncode == 0 and generated.exists(), f"Pluto failed:\n{producer.stdout}")
        require(
            "[Pluto] After intra_tile reschedule" in producer.stdout,
            "diamond hyperplane restore did not run under --nointratileopt",
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O0", work_source, "-o", baseline_exe])
        optimized_build = run([compiler, "-O0", generated, "-o", optimized_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")
        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        optimized = parse_int_output("fixed Pluto execution", run([optimized_exe]))
        require(baseline == 20 and optimized == baseline, f"unexpected results: {baseline}, {optimized}")
        print(
            f"[pluto-diamond-nointra] producer: expected={baseline} actual={optimized} "
            "consistency=match interpretation=mandatory-diamond-restore-ran"
        )

        env = os.environ.copy()
        env["POLCERT_PLUTO"] = str(pluto)
        env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked_work = work / "checked-phases"
        checked_work.mkdir()
        checked = run(
            [polopt, *POLCERT_FLAGS, "--tile-sizes-file", tile_sizes, fixture / "input.loop"],
            cwd=checked_work,
            env=env,
            timeout=120,
        )
        require(
            checked.returncode == 0
            and checked.stdout.count("[tiling-validation] route=permutable-band") == 1
            and "[alarm]" not in checked.stdout
            and "actual-schedule" not in checked.stdout
            and "Assertion" not in checked.stdout,
            "diamond did not complete through direct tiling validation:\n"
            + checked.stdout,
        )
        require(checked.stdout.count("== Optimized Loop ==\n") == 1,
                "accepted route did not emit exactly one optimized loop")
        optimized_loop = checked.stdout.split("== Optimized Loop ==\n", 1)[1]
        optimized_loop = '\n'.join(line for line in optimized_loop.splitlines()
                                   if line.strip() != '[tiling-validation] route=permutable-band')
        check_array_states(source.read_text(), optimized_loop, work, compiler, run)
        candidates = list(checked_work.glob("polcert*.scop.posttile.scop"))
        require(len(candidates) == 1, f"expected one checked tiled proposal, got {candidates}")
        posttile = candidates[0]
        midpoint = posttile.with_name(posttile.name.replace(".posttile.scop", ".midtransform.scop"))
        require_preserved_raw_edge(midpoint, posttile)
        direct = run([repo / "polcert", "--tiling", midpoint, posttile], cwd=work, env=env)
        require(direct.returncode == 0 and "(route=permutable-band)" in direct.stdout
                and "actual-schedule" not in direct.stdout,
                "intermediate candidate did not pass direct tiling validation:\n" + direct.stdout)
        before = posttile.with_name(posttile.name.replace('.posttile.scop', '.beforescheduling.scop'))
        after = posttile.with_name(posttile.name.replace('.posttile.scop', '.afterscheduling.scop'))
        phases = run([repo / 'polcert', before, midpoint, posttile, after], cwd=work, env=env)
        require(phases.returncode == 0
                and '[PHASE] affine(before, mid): OK' in phases.stdout
                and '[PHASE] tiling(mid, posttile): OK route=permutable-band' in phases.stdout
                and '[PHASE] affine(posttile, after): OK' in phases.stdout,
                'diamond phase validation failed:\n' + phases.stdout)
        print(
            "[pluto-diamond-nointra] checked-pipeline: expected=direct-tiling,affine,codegen "
            "actual=accepted interpretation=valid-tiling-boundary-and-matching-array-states"
        )
        rar_work = work / 'rar-phases'
        rar_work.mkdir()
        rar = run([polopt, *POLCERT_FLAGS, "--rar", "--tile-sizes-file", tile_sizes,
                   fixture / "input.loop"], cwd=rar_work, env=env)
        require(rar.returncode == 0
                and rar.stdout.count("[tiling-validation] route=permutable-band") == 1
                and "[alarm]" not in rar.stdout
                and "actual-schedule" not in rar.stdout
                and "Assertion" not in rar.stdout
                and rar.stdout.count("== Optimized Loop ==\n") == 1,
                "RAR diamond compilation failed:\n" + rar.stdout)
        rar_loop = rar.stdout.split("== Optimized Loop ==\n", 1)[1]
        rar_loop = '\n'.join(line for line in rar_loop.splitlines()
                             if line.strip() != '[tiling-validation] route=permutable-band')
        check_array_states(source.read_text(), rar_loop, rar_work, compiler, run)
        rar_candidates = list(rar_work.glob('polcert*.scop.posttile.scop'))
        require(len(rar_candidates) == 1, 'missing unique RAR phase dump')
        rar_post = rar_candidates[0]
        rar_phases = [rar_post.with_name(rar_post.name.replace('.posttile.scop', suffix))
                      for suffix in ('.beforescheduling.scop', '.midtransform.scop',
                                     '.posttile.scop', '.afterscheduling.scop')]
        validated = run([repo / 'polcert', *rar_phases], cwd=rar_work, env=env)
        require(validated.returncode == 0
                and '[PHASE] affine(before, mid): OK' in validated.stdout
                and '[PHASE] tiling(mid, posttile): OK route=permutable-band' in validated.stdout
                and '[PHASE] affine(posttile, after): OK' in validated.stdout,
                'RAR phase validation failed:\n' + validated.stdout)
        print("[pluto-diamond-nointra] rar-pipeline: direct-tiling,affine,codegen=accepted "
              "complete-array-states=match")

    print("[pluto-diamond-nointra] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-diamond-nointra] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
