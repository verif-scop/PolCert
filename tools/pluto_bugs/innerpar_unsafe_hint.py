#!/usr/bin/env python3
"""Test-only adversarial hint wrapper; preserve every producer relation byte."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def relation(text, kind, occurrence=0):
    lines = text.splitlines()
    start = [i for i, line in enumerate(lines) if line == kind][occurrence] + 1
    numeric = []
    for line in lines[start:]:
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        numeric.append([int(x) for x in line.split()])
        if len(numeric) == numeric[0][0] + 1:
            if len(numeric[0]) != 6 or any(len(row) != numeric[0][1] for row in numeric[1:]):
                raise AssertionError('malformed relation dimensions')
            return numeric[0], numeric[1:]
    raise AssertionError('incomplete relation')


def unsafe_hint(text):
    domain, constraints = relation(text, 'DOMAIN')
    scatter, equations = relation(text, 'SCATTERING')
    dims = domain[2]
    if dims not in (4, 5) or domain[3:] != [0, 0, 0] or scatter[2:] != [8, dims, 0, 0]:
        raise AssertionError('unsupported innerpar witness shape')
    # A[2][2] reads A[2][1]. Their i tile is the same; their j tiles differ.
    points = ([1, 0, 2, 1], [1, 1, 2, 2]) if dims == 4 else ([1, 0, 0, 2, 1], [1, 0, 1, 2, 2])
    def access(kind, occurrence, point):
        header, rows = relation(text, kind, occurrence)
        if header[2:] != [3, dims, 0, 0]:
            raise AssertionError('unsupported dependence access shape')
        values = []
        for index, row in enumerate(rows):
            if row[0] != 0 or row[1:4] != [-int(i == index) for i in range(3)]:
                raise AssertionError('nonfunctional access')
            values.append(sum(a*b for a, b in zip(row[4:-1], point)) + row[-1])
        return values
    written = access('WRITE', 0, points[0])
    reads = [access('READ', i, points[1]) for i in range(text.splitlines().count('READ'))]
    if written != [1, 2, 1] or written not in reads:
        raise AssertionError('candidate relations lack the claimed read-after-write dependence')
    schedules = []
    for point in points:
        for row in constraints:
            value = sum(a*b for a, b in zip(row[1:-1], point)) + row[-1]
            if not (value == 0 if row[0] == 0 else value >= 0):
                raise AssertionError('dependence witness is outside the producer domain')
        schedule = []
        for index, row in enumerate(equations):
            if row[0] != 0 or row[1:9] != [-int(i == index) for i in range(8)]:
                raise AssertionError('nonfunctional or reordered scattering')
            schedule.append(sum(a*b for a, b in zip(row[9:-1], point)) + row[-1])
        schedules.append(schedule)
    differences = [i for i, (a, b) in enumerate(zip(*schedules)) if a != b]
    if not differences or differences[0] != 3:
        raise AssertionError('expected dependence-carrying tile coordinate absent')
    names = re.search(r'<scatnames>\s*(.*?)\s*</scatnames>', text, re.S).group(1).split()
    if len(names) != 8:
        raise AssertionError('missing scattering names')
    hint = '<loop>\n1\n' + names[3] + '\n1\n1\n' + ','.join(names[4:]) + '\n1\n</loop>'
    without_hint = re.sub(r'<loop>.*?</loop>', '', text, flags=re.S)
    result = without_hint.replace('</OpenScop>', hint + '\n</OpenScop>')
    witness = dict(source_instance=[2, 1], destination_instance=[2, 2],
                   domain_points=points, schedules=schedules, raw_coordinate=3,
                   source_write=written, destination_reads=reads,
                   hinted_iterator=names[3], earlier_schedule_coordinates_equal=True)
    return result, witness


def main():
    result = subprocess.run([os.environ['POLCERT_INNERPAR_REAL_PLUTO'], *sys.argv[1:]])
    if result.returncode:
        return result.returncode
    output = Path(sys.argv[-1] + '.afterscheduling.scop')
    changed, witness = unsafe_hint(output.read_text())
    output.write_text(changed)
    Path(os.environ['POLCERT_INNERPAR_HINT_WITNESS']).write_text(json.dumps(witness, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
