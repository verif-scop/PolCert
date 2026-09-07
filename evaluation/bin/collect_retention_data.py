#!/usr/bin/env python3
"""Capture Pluto proposals and final PolCert loops for paired effect analysis.

The Pluto wrapper records the actual optimizer output before validation. It
does not alter flags, schedules, certificates, or validator behavior. Counts
are derived from the saved outputs, never from a requested optimization flag.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from retention_baseline import collect_baseline


COMMON = ["--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam"]
CONFIGURATIONS = {
    "affine": ["--notile", *COMMON, "--nodiamond-tile", "--noparallel"],
    "rectangular": ["--tile", *COMMON, "--nodiamond-tile", "--noparallel"],
    "two-level": ["--tile", "--second-level-tile", *COMMON, "--nodiamond-tile", "--noparallel"],
    "parallel": ["--tile", *COMMON, "--nodiamond-tile", "--parallel", "--innerpar"],
    "diamond": ["--tile", *COMMON, "--diamond-tile", "--noparallel"],
    "iss": ["--tile", "--iss", *COMMON, "--nodiamond-tile", "--noparallel"],
    "two-level-parallel": ["--tile", "--second-level-tile", *COMMON, "--nodiamond-tile", "--parallel", "--innerpar"],
    "diamond-parallel": ["--tile", *COMMON, "--diamond-tile", "--parallel", "--innerpar"],
    "diamond-two-level": ["--tile", "--second-level-tile", *COMMON, "--diamond-tile", "--noparallel"],
}
PHASE_SUFFIXES = [
    ".beforescheduling.scop", ".midtransform.scop", ".posttile.scop",
    ".afterscheduling.scop", ".pluto.c", ".pluto.cloog",
]


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def serial_tail(row):
    return ('--second-level-tile' in row['pluto_args'] and row['kernel'] in {
        'adi', 'advect3d', 'fdtd-1d', 'fdtd-2d', 'jacobi-1d-imper',
        'jacobi-2d', 'jacobi-batch', 'negparam'}) or row['kernel'] == 'heat-3d-imperfect'


def wait_for_memory(minimum_gib):
    if not minimum_gib:
        return
    while True:
        match = re.search(r'^MemAvailable:\s+(\d+)\s+kB$', Path('/proc/meminfo').read_text(), re.MULTILINE)
        if match is None:
            raise ValueError('Cannot enforce memory admission: MemAvailable is missing')
        if int(match[1]) >= minimum_gib * 1024 * 1024:
            return
        # Admission only: never terminate another running case, and do not
        # include queueing time in a case's producer/native deadline.
        time.sleep(2)


def stage_iss_helper(source_root, work, expected_sha):
    source = source_root / 'tools/iss/pluto_iss_check.py'
    if sha(source) != expected_sha:
        raise ValueError('ISS helper changed after provenance capture: ' + str(source))
    target = work / 'tools/iss/pluto_iss_check.py'
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        if sha(target) != expected_sha:
            raise ValueError('Refusing incompatible staged ISS helper: ' + str(target))
    else:
        shutil.copy2(source, target)
    return target


def capture_pluto(argv):
    actual = os.environ["RETENTION_REAL_PLUTO"]
    root = Path(os.environ["RETENTION_CAPTURE_DIR"])
    invocation = root / str(time.time_ns())
    invocation.mkdir(parents=True)
    inputs = [Path(arg).absolute() for arg in argv if arg.endswith(".scop") and Path(arg).is_file()]
    if inputs:
        shutil.copy2(inputs[-1], invocation / "input.scop")
    result = subprocess.run([actual, *argv], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (invocation / "stdout.txt").write_bytes(result.stdout)
    (invocation / "stderr.txt").write_bytes(result.stderr)
    files = {}
    if inputs:
        for suffix in PHASE_SUFFIXES:
            candidates = [Path(str(inputs[-1]) + suffix), Path.cwd() / (inputs[-1].name + suffix)]
            for candidate in candidates:
                if candidate.is_file():
                    name = "output" + suffix
                    shutil.copy2(candidate, invocation / name)
                    files[suffix] = name
                    break
    dump(invocation / "invocation.json", {
        "argv": [actual, *argv], "cwd": str(Path.cwd()),
        "returncode": result.returncode, "input": str(inputs[-1]) if inputs else None,
        "files": files,
    })
    sys.stdout.buffer.write(result.stdout)
    sys.stderr.buffer.write(result.stderr)
    return result.returncode


def make_manifest(source, container_source):
    cases = []
    sources = sorted((source / "tests/polopt-generated/inputs").glob("*.loop"))
    extra = [
        "tests/polopt-regression/inputs/nodep.loop",
        "tests/polopt-regression/inputs/triple-nodep.loop",
        "tools/second_level_tiling/fixtures/matmul-init.loop",
        "tools/second_level_tiling/fixtures/symbolic-independent-2d.loop",
        "tools/parallel_current/fixtures/diamond-example-inner-batch.loop",
        "tools/parallel_current/fixtures/jacobi-batch.loop",
    ]
    existing = {path.stem for path in sources}
    sources.extend(source / rel for rel in extra if Path(rel).stem not in existing)
    for loop in sources:
        rel = loop.relative_to(source)
        configs = list(CONFIGURATIONS)[:6]
        if "fixtures" in rel.parts or loop.stem in {"matmul", "jacobi-1d-imper", "jacobi-2d-imper", "nodep", "triple-nodep"}:
            configs += list(CONFIGURATIONS)[6:]
        for config in configs:
            c_rel = Path("tests/pluto-all") / loop.stem / (loop.stem + ".c")
            c_path = str(container_source / c_rel) if (source / c_rel).is_file() else None
            cases.append({
                "id": loop.stem + "--" + config,
                "kernel": loop.stem,
                "configuration": config,
                "loop_input": str(container_source / rel),
                "c_source": c_path,
                "source_relative": str(rel),
                "source_sha256": sha(loop),
                "polopt_args": ["--pluto-compat", *CONFIGURATIONS[config]],
                "pluto_args": CONFIGURATIONS[config],
            })
    assert len({row["id"] for row in cases}) == len(cases)
    return {
        "schema_version": 1,
        "source_root": str(container_source),
        "selection": "All 62 corpus kernels under six configurations; four additional existing fixtures and selected combined configurations. RAR is disabled throughout, matching PolCert's native default.",
        "cases": cases,
    }


def collect(args):
    manifest = json.loads(args.manifest.read_text())
    root = args.output.absolute()
    root.mkdir(parents=True, exist_ok=True)
    wrapper = root / "pluto-capture"
    wrapper.write_text("#!/bin/sh\nexec python3 " + str(Path(__file__).absolute()) + " --capture-pluto \"$@\"\n")
    wrapper.chmod(0o755)
    helper = args.source_root / 'tools/iss/pluto_iss_check.py'
    provenance = {
        "polopt": str(args.polopt), "polopt_sha256": sha(args.polopt),
        "pluto": str(args.pluto), "pluto_sha256": sha(args.pluto),
        "collector_sha256": sha(Path(__file__)), "started_at": time.time(),
        "manifest_sha256": sha(args.manifest),
        "timeout_seconds": args.timeout,
        "iss_helper": str(helper), "iss_helper_sha256": sha(helper),
        "independent_baseline": args.independent_baseline,
        "baseline_timeout_seconds": args.baseline_timeout,
        "baseline_script_sha256": sha(Path(__file__).with_name('retention_baseline.py')),
        "workers": args.workers, "minimum_available_gib": args.minimum_available_gib,
    }
    if (root / "provenance.json").exists():
        previous = json.loads((root / "provenance.json").read_text())
        for key in ["polopt_sha256", "pluto_sha256", "collector_sha256", "manifest_sha256", "iss_helper_sha256",
                    "independent_baseline", "baseline_timeout_seconds", "baseline_script_sha256",
                    "timeout_seconds", "workers", "minimum_available_gib"]:
            if previous.get(key) != provenance[key]:
                raise SystemExit("Refusing incompatible resume: " + key)
    else:
        dump(root / "manifest.json", manifest)
        dump(root / "provenance.json", provenance)
    selected = [row for row in manifest["cases"]
                if (not args.configuration or row["configuration"] in args.configuration)
                and (not args.kernel or row["kernel"] in args.kernel)]
    def collect_one(indexed):
        index, row = indexed
        if sha(Path(row["loop_input"])) != row["source_sha256"]:
            raise SystemExit("Source changed: " + row["loop_input"])
        if sha(args.polopt) != provenance['polopt_sha256'] or sha(args.pluto) != provenance['pluto_sha256']:
            raise SystemExit('Frozen compiler or producer binary changed during collection')
        case = root / "cases" / row["id"]
        if (case / "result.json").is_file() and not args.rerun:
            return
        if args.independent_baseline and (case / 'baseline').exists():
            raise ValueError('Incomplete independent pair must be preserved and retried in a new collection: ' + row['id'])
        wait_for_memory(args.minimum_available_gib)
        case.mkdir(parents=True, exist_ok=True)
        source_copy = case / 'source.loop'
        if source_copy.exists() and sha(source_copy) != row['source_sha256']:
            raise ValueError('Archived source changed: ' + row['id'])
        if not source_copy.exists():
            shutil.copy2(row['loop_input'], source_copy)
        work = case / "work"
        work.mkdir(exist_ok=True)
        staged_helper = stage_iss_helper(args.source_root, work, provenance['iss_helper_sha256'])
        env = os.environ.copy()
        env.update({"POLCERT_PLUTO": str(wrapper), "RETENTION_REAL_PLUTO": str(args.pluto),
                    "RETENTION_CAPTURE_DIR": str(case / "pluto"),
                    "COMPCERT_CONFIG": str(args.source_root / "tests/pluto/polcert.ini")})
        if args.independent_baseline:
            collect_baseline(case, row, args.polopt, args.pluto, wrapper, env, args.baseline_timeout)
        command = [str(args.polopt), *row["polopt_args"], row["loop_input"]]
        start = time.monotonic()
        process = subprocess.Popen(command, cwd=str(work), env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            import signal
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        (case / "polcert.stdout.txt").write_bytes(stdout)
        (case / "polcert.stderr.txt").write_bytes(stderr)
        dump(case / "result.json", {
            **row, "command": command, "returncode": process.returncode,
            "timed_out": timed_out, "wall_seconds": time.monotonic() - start,
            "iss_helper_sha256": sha(staged_helper),
            "polopt_sha256": provenance['polopt_sha256'], "pluto_sha256": provenance['pluto_sha256'],
        })
        print("[{}/{}] {} exit={} timeout={}".format(index, len(selected), row["id"], process.returncode, timed_out), flush=True)
    indexed = list(enumerate(selected, 1))
    normal = [item for item in indexed if not serial_tail(item[1])]
    tails = [item for item in indexed if serial_tail(item[1])]
    with ThreadPoolExecutor(max_workers=args.workers) as workers:
        list(workers.map(collect_one, normal))
    for item in tails:
        collect_one(item)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--capture-pluto":
        return capture_pluto(sys.argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--container-source", type=Path, default=Path("/tmp/polcert-eval-current"))
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--make-manifest", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--polopt", type=Path)
    parser.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--independent-baseline", action="store_true")
    parser.add_argument("--baseline-timeout", type=int, default=300)
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--minimum-available-gib', type=int, default=0)
    parser.add_argument("--configuration", action="append")
    parser.add_argument("--kernel", action="append")
    parser.add_argument("--rerun", action="store_true")
    args = parser.parse_args()
    if args.workers not in (1, 2, 3) or args.minimum_available_gib < 0:
        parser.error('Use 1–3 workers and a nonnegative memory admission threshold')
    if args.independent_baseline and args.rerun:
        parser.error('Independent paired runs require a fresh output directory, not --rerun')
    if args.make_manifest:
        dump(args.manifest, make_manifest(args.source_root, args.container_source))
        return 0
    if args.polopt is None:
        args.polopt = args.source_root / "polopt"
    collect(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
