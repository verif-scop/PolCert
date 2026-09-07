"""Observe complete dynamic parallel-region membership, without old results.

Records identify read/write objects and their indices, not arithmetic values.
The C instrumentation and its explicit resource limits are shared with the
existing parallel observer; this module contains no capture-selection logic.
"""
import collections
import hashlib
import json
import subprocess

import parallel_trace_helpers as review


def digest(records):
    return hashlib.sha256(b'\n'.join(records)).hexdigest()


def parse_output(stdout, returncode):
    records = []
    regions = collections.defaultdict(lambda: collections.defaultdict(list))
    seen, conflict = {}, None
    for line in stdout.splitlines():
        if '|' not in line:
            continue
        fields = line.split('|')
        context = [tuple(map(int, item.split(':')))
                   for item in fields[0].rstrip(',').split(',') if item]
        record = json.dumps(fields[1:], separators=(',', ':')).encode()
        records.append(record)
        for region, iteration in context:
            regions[region][iteration].append(record)
        values, cursor = list(map(int, fields[2:])), 0
        for access in fields[1].split(';'):
            mode, location = access.split(':', 1)
            dimensions = location.count('[]')
            address = (location.replace('[]', ''), tuple(values[cursor:cursor + dimensions]))
            cursor += dimensions
            if mode not in ('W', 'R'):
                continue
            for region, iteration in context:
                history = seen.setdefault((region, address), {'readers': {}, 'writers': {}})
                candidates = list(history['writers'].values())
                if mode == 'W':
                    candidates += list(history['readers'].values())
                previous = next((entry for entry in candidates if entry['iteration'] != iteration), None)
                entry = {'iteration': iteration, 'mode': mode, 'record': fields[1:], 'ordinal': len(records)}
                if previous and conflict is None:
                    conflict = {'region': region, 'address': address, 'first': previous,
                                'second': entry}
                # Two distinct iteration IDs per access mode suffice: any
                # later access must differ from at least one of those two.
                bucket = history['writers' if mode == 'W' else 'readers']
                if len(bucket) < 2:
                    bucket.setdefault(iteration, entry)
        if cursor != len(values):
            raise ValueError('Access record arity mismatch')
    groups = [sorted((len(items), digest(sorted(items))) for items in threads.values())
              for threads in regions.values() if len(threads) >= 2]
    return {'complete': returncode == 0 and stdout.rstrip().endswith('COMPLETE'),
            'returncode': returncode, 'statements': len(records),
            'duplicate_access_records': len(records) - len(set(records)),
            'distinct_access_records': len(set(records)),
            'ordered_access_sha256': digest(records), 'access_multiset_sha256': digest(sorted(records)),
            'nontrivial_regions': len(groups), 'membership_groups': sorted(groups), 'first_conflict': conflict}


def run(executable, values):
    result = subprocess.run([str(executable), *map(str, values)], capture_output=True,
                            text=True, timeout=15)
    return parse_output(result.stdout, result.returncode)
