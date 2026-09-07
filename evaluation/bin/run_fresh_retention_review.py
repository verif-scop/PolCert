#!/usr/bin/env python3
"""Analyze fresh paired outputs in a versioned, separate workspace.

Raw records are linked read-only by convention; all generated observers and
reviews are written below --output. Nothing reads historical trace results.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bounded_run(command, timeout):
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(command, timeout, output=stdout, stderr=stderr)
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def link_case(raw, destination):
    destination.mkdir(parents=True, exist_ok=True)
    names = ['result.json', 'source.loop', 'polcert.stdout.txt', 'polcert.stderr.txt', 'baseline', 'pluto']
    names += [path.name for path in raw.glob('producer-resource-*.json')]
    for name in names:
        source, target = raw / name, destination / name
        if not source.exists():
            continue
        if target.is_symlink():
            if target.resolve() != source.resolve():
                raise ValueError('Review workspace points at a different raw case')
        elif target.exists():
            raise ValueError('Refusing preexisting mutable raw copy in review workspace')
        else:
            target.symlink_to(source.resolve(), target_is_directory=source.is_dir())


def run(args):
    plan = json.loads(args.plan.read_text())
    raw_identity = args.raw / 'run-provenance.json'
    args.output.mkdir(parents=True, exist_ok=True)
    scripts = ['run_fresh_retention_review.py', 'analyze_retention_data.py', 'retention_scop.py',
               'retention_trace.py', 'retention_candidate.py', 'retention_baseline.py', 'retention_identity.py',
               'review_parallel_recollection.py', 'parallel_membership_observer.py', 'review_parallel_retention.py']
    identity = {'measurement_run_sha256': sha(raw_identity), 'plan_sha256': sha(args.plan),
                'old_trace_reuse': False, 'scripts_sha256': {name: sha(Path(__file__).with_name(name)) for name in scripts}}
    identity_path = args.output / 'review-provenance.json'
    if identity_path.exists() and json.loads(identity_path.read_text()) != identity:
        raise ValueError('Use a new review directory after changing observer inputs')
    identity_path.write_text(json.dumps(identity, indent=2) + '\n')

    def analyze(job):
        cohort, raw = job
        root = args.output / cohort
        case = root / 'cases' / raw.name
        link_case(raw, case)
        command = [sys.executable, str(Path(__file__).with_name('analyze_retention_data.py')),
                   str(root), '--source-root', str(args.source_root), '--case', str(case)]
        started = time.monotonic()
        try:
            run = bounded_run(command, timeout=90)
            state = {'returncode': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
        except subprocess.TimeoutExpired:
            state = {'returncode': None, 'status': 'observer-timeout'}
        state.update(measurement_run_sha256=identity['measurement_run_sha256'],
                     observer_seconds=time.monotonic() - started, command=command)
        (case / 'analysis-run.json').write_text(json.dumps(state, indent=2) + '\n')
        if cohort in ('standard-parallel', 'legacy-innerpar') and state['returncode'] == 0:
            command = [sys.executable, str(Path(__file__).with_name('review_parallel_recollection.py')),
                       str(root), '--fresh', '--repository', str(args.raw), '--source-root', str(args.source_root),
                       '--observer', str(Path(__file__).with_name('parallel_membership_observer.py')),
                       '--output', str(root / 'parallel' / raw.name), '--only', raw.name]
            try:
                run = bounded_run(command, timeout=120)
                (case / 'parallel-review-run.json').write_text(json.dumps({
                    'command': command, 'returncode': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr,
                    'measurement_run_sha256': identity['measurement_run_sha256']}, indent=2) + '\n')
            except subprocess.TimeoutExpired:
                (case / 'parallel-review-run.json').write_text(json.dumps({'status': 'observer-timeout', 'command': command}) + '\n')
        print(cohort + '/' + raw.name, state['returncode'], flush=True)

    while True:
        jobs = []
        complete = True
        for item in plan['collections']:
            cohort = item['cohort']
            records = sorted((args.raw / item['result_directory'] / 'cases').glob('*/result.json'))
            complete = complete and len(records) == item['pairs']
            for record in records:
                if not (args.output / cohort / 'cases' / record.parent.name / 'analysis-run.json').exists():
                    jobs.append((cohort, record.parent))
        with ThreadPoolExecutor(max_workers=args.workers) as workers:
            list(workers.map(analyze, jobs))
        if not args.follow or complete:
            return
        time.sleep(5)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--raw', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, choices=[1, 2], default=2)
    parser.add_argument('--follow', action='store_true')
    run(parser.parse_args())


if __name__ == '__main__':
    main()
