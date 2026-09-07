#!/usr/bin/env python3
"""Collect every frozen cohort, with bounded workers and producer resources."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    plan = json.loads(args.plan.read_text())
    args.output.mkdir(parents=True, exist_ok=True)
    provenance = {'plan_sha256': sha(args.plan), 'compiler': str(args.polopt),
                  'compiler_sha256': sha(args.polopt), 'producer': str(args.pluto),
                  'producer_sha256': sha(args.pluto), 'script_sha256': sha(Path(__file__)),
                  'collector_sha256': sha(Path(__file__).with_name('collect_retention_data.py')),
                  'resource_monitor_sha256': sha(Path(__file__).with_name('watch_retention_resources.py'))}
    identity = args.output / 'run-provenance.json'
    if identity.exists() and json.loads(identity.read_text()) != provenance:
        raise ValueError('Refusing a changed paired-run identity')
    identity.write_text(json.dumps(provenance, indent=2) + '\n')
    results = []
    for collection in plan['collections']:
        name = collection['cohort']
        manifest = args.plan.parent / collection['manifest']
        if sha(manifest) != collection['manifest_sha256']:
            raise ValueError('Manifest changed: ' + name)
        directory = args.output / collection['result_directory']
        directory.mkdir(exist_ok=True)
        # The monitor needs only the frozen manifest; the collector validates
        # and rewrites it identically when it creates its provenance file.
        target_manifest = directory / 'manifest.json'
        if target_manifest.exists() and target_manifest.read_bytes() != manifest.read_bytes():
            raise ValueError('Collection manifest changed: ' + name)
        target_manifest.write_bytes(manifest.read_bytes())
        command = [sys.executable, str(Path(__file__).with_name('collect_retention_data.py')),
                   '--source-root', str(args.source_root), '--polopt', str(args.polopt),
                   '--pluto', str(args.pluto), '--manifest', str(manifest), '--output', str(directory),
                   '--independent-baseline', '--baseline-timeout', str(plan['producer_seconds']),
                   '--timeout', str(plan['native_seconds']), '--workers', str(plan['native_workers']),
                   '--minimum-available-gib', '12']
        watcher_command = [sys.executable, str(Path(__file__).with_name('watch_retention_resources.py')),
                           str(directory), '--producer', str(args.pluto), '--deadline', str(plan['producer_seconds']),
                           '--rss-cap-mib', str(plan['producer_rss_mib'])]
        print('Starting ' + name + ': ' + str(collection['pairs']) + ' pairs', flush=True)
        (directory / 'collection-command.json').write_text(json.dumps(command, indent=2) + '\n')
        start = time.monotonic()
        with (directory / 'collection.log').open('a') as log, (directory / 'resource-monitor.log').open('a') as resource_log:
            watcher = subprocess.Popen(watcher_command, stdout=resource_log, stderr=subprocess.STDOUT)
            try:
                completed = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
            finally:
                if watcher.poll() is None:
                    watcher.terminate()
                watcher.wait()
        result = {'cohort': name, 'returncode': completed.returncode,
                  'elapsed_seconds': time.monotonic() - start,
                  'recorded_pairs': len(list((directory / 'cases').glob('*/result.json')))}
        results.append(result)
        (args.output / 'collection-progress.json').write_text(json.dumps(results, indent=2) + '\n')
        print(json.dumps(result), flush=True)
        if completed.returncode:
            raise SystemExit(completed.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--polopt', type=Path, required=True)
    parser.add_argument('--pluto', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args())


if __name__ == '__main__':
    main()
