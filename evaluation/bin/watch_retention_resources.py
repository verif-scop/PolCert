#!/usr/bin/env python3
"""Bound external producer resources without relabeling validator outcomes."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import time


def producer_record(proc, executable, root):
    try:
        argv = (proc / 'cmdline').read_bytes().rstrip(b'\0').split(b'\0')
        argv = [value.decode() for value in argv]
        if not argv or Path(argv[0]).resolve() != executable.resolve():
            return None
        inputs = []
        for arg in argv[1:]:
            path = Path(arg)
            if not arg.endswith('.scop') or not path.is_absolute():
                continue
            path = path.resolve()
            try:
                relative = path.relative_to(root)
            except ValueError:
                continue
            if len(relative.parts) >= 4 and relative.parts[0] == 'cases' and relative.parts[2] == 'work':
                inputs.append((path, relative.parts[1]))
        if not inputs:
            return None
        path, case = inputs[-1]
        status = (proc / 'status').read_text()
        match = re.search(r'^VmRSS:\s+(\d+)\s+kB$', status, re.MULTILINE)
        rss = int(match[1]) if match else 0
        stat = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
        elapsed = float(Path('/proc/uptime').read_text().split()[0]) - int(stat[19]) / os.sysconf('SC_CLK_TCK')
        return {'pid': int(proc.name), 'argv': argv, 'case': case,
                'elapsed_seconds': elapsed, 'rss_kib': rss, 'input': str(path),
                'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    except (OSError, ValueError, IndexError, UnicodeError):
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--producer', type=Path, required=True)
    parser.add_argument('--deadline', type=int, default=300)
    parser.add_argument('--rss-cap-mib', type=int, default=12288)
    parser.add_argument('--once', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    policy = {'producer_deadline_seconds': args.deadline,
              'producer_rss_cap_mib': args.rss_cap_mib,
              'producer': str(args.producer),
              'producer_sha256': hashlib.sha256(args.producer.read_bytes()).hexdigest(),
              'classification': 'external-producer-resource-limit',
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    policy_file = root / 'producer-resource-policy.json'
    if policy_file.exists() and json.loads(policy_file.read_text()) != policy:
        raise ValueError('Resource policy changed during a collection')
    policy_file.write_text(json.dumps(policy, indent=2) + '\n')
    planned = len(json.loads((root / 'manifest.json').read_text())['cases'])
    while True:
        for proc in Path('/proc').iterdir():
            if not proc.name.isdigit():
                continue
            row = producer_record(proc, args.producer, root)
            if row is None:
                continue
            limits = []
            if row['elapsed_seconds'] > args.deadline:
                limits.append('producer-deadline')
            if row['rss_kib'] > args.rss_cap_mib * 1024:
                limits.append('producer-rss-cap')
            if not limits:
                continue
            row.update({'limits_exceeded': limits, 'policy': policy,
                        'action': 'SIGKILL external producer only; preserve driver outcome and raw inputs'})
            target = root / 'cases' / row['case'] / ('producer-resource-' + str(row['pid']) + '.json')
            target.write_text(json.dumps(row, indent=2) + '\n')
            try:
                os.kill(row['pid'], signal.SIGKILL)
                row['signal_sent'] = True
            except ProcessLookupError:
                row['signal_sent'] = False
            target.write_text(json.dumps(row, indent=2) + '\n')
            print(json.dumps(row), flush=True)
        if args.once or len(list((root / 'cases').glob('*/result.json'))) >= planned:
            return
        time.sleep(1)


if __name__ == '__main__':
    main()
