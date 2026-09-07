#!/usr/bin/env python3
"""Compare genuine source-domain partitions in the three reverse ISS fixtures.

Both independently compiled outputs must split assignment sites at the same
half-domain cut. The existing native fixture harness also checks each source
iteration once and numerical results over ten odd/even boundary samples.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

from retention_candidate import select_candidate
from retention_scop import analyze_producer


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_arguments(text):
    parts, start, depth = [], 0, 0
    for index, character in enumerate(text):
        depth += (character == '(') - (character == ')')
        if depth < 0:
            raise ValueError('Unbalanced statement arguments')
        if character == ',' and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
    if depth:
        raise ValueError('Unbalanced statement arguments')
    return parts + [text[start:].strip()]


def expand_statement_macros(code):
    """Expand only complete statement calls; leave loop bounds unchanged."""
    macros = {}
    lines = []
    for line in code.splitlines():
        definition = re.match(r'^\s*#define\s+(S\d+)\(([^)]*)\)\s*(.*)$', line)
        if definition:
            macros[definition[1]] = (split_arguments(definition[2]), definition[3])
        else:
            lines.append(line)
    result = []
    for line in lines:
        call = re.match(r'^\s*(S\d+)\((.*)\)\s*;?\s*$', line)
        if call:
            if call[1] not in macros:
                raise ValueError('Statement call has no captured macro')
            formal, body = macros[call[1]]
            actual = split_arguments(call[2])
            if len(formal) != len(actual):
                raise ValueError('Statement macro arity mismatch')
            replacements = dict(zip(formal, actual))
            body = re.sub(r'(?<![\w$])[$A-Za-z_][\w$]*',
                          lambda m: '(' + replacements[m[0]] + ')' if m[0] in replacements else m[0], body)
            result.append(body)
        else:
            if re.search(r'\bS\d+\s*\(', line):
                raise ValueError('Unsupported embedded statement call')
            if line.lstrip().startswith('#include'):
                continue
            # Use the same exact integer helpers as the native observer.
            if re.match(r'\s*#define\s+(?:floord|ceild)\b', line):
                continue
            result.append(line)
    if not macros:
        raise ValueError('No statement macros in independent Pluto output')
    return '#define floord(a,b) polcert_z_div((a),(b))\n#define ceild(a,b) (-polcert_z_div(-(a),(b)))\n' + '\n'.join(result)


def review_case(case, target, helper):
    raw = json.loads((case / 'result.json').read_text())
    selected = select_candidate(case)
    row = {'id': raw['id'], 'cohort': 'iss-supplement', 'effect': 'iss',
           'source_sha256': raw['source_sha256'], 'producer_status': 'unknown',
           'retention_status': 'requires-partition-review'}
    if selected['status'] != 'selected':
        return {**row, 'retention_status': 'baseline-unavailable', 'selection': selected}
    producer_file = Path(selected['selected']['file'])
    final_file = case / 'polcert.stdout.txt'
    row.update(producer_sha256=sha(producer_file), final_sha256=sha(final_file))
    actual = analyze_producer(case)['effects']['iss']['status']
    row['producer_status'] = actual
    if actual == 'absent':
        return {**row, 'retention_status': 'not-applicable'}
    if actual != 'observed' or raw['returncode'] or raw['timed_out']:
        return row
    source = (case / 'source.loop').read_text()
    final = final_file.read_text().split('== Optimized Loop ==', 1)[1].strip()
    expanded = expand_statement_macros(producer_file.read_text())
    target.mkdir(parents=True, exist_ok=False)
    row['checks'] = []
    original_transpiler = helper.transpile_loop_text
    for name, text in [('pluto', expanded), ('polcert', final)]:
        # Reuse the already-tested fixture checks. Only the Pluto side enters
        # as C; its statement macros have been expanded without changing bounds.
        helper.transpile_loop_text = lambda value: expanded if value is expanded else original_transpiler(value)
        try:
            code, sites = helper.harness(source, text, raw['iss_rank'], raw['iss_cut_axis'])
        finally:
            helper.transpile_loop_text = original_transpiler
        c_file, binary = target / (name + '.c'), target / name
        c_file.write_text(code)
        command = ['gcc', '-O0', '-std=gnu11', str(c_file), '-o', str(binary)]
        built = subprocess.run(command, capture_output=True, text=True, timeout=15)
        (target / (name + '.build.stderr.txt')).write_text(built.stderr)
        check = {'side': name, 'build_command': command, 'build_returncode': built.returncode,
                 'assignment_sites': sites, 'harness_sha256': sha(c_file)}
        if built.returncode == 0:
            observed = subprocess.run([str(binary)], capture_output=True, text=True, timeout=30)
            (target / (name + '.stdout.txt')).write_text(observed.stdout)
            (target / (name + '.stderr.txt')).write_text(observed.stderr)
            check.update(returncode=observed.returncode, complete_samples=len(observed.stdout.splitlines()))
        row['checks'].append(check)
    if all(check.get('returncode') == 0 and check['complete_samples'] == 10 for check in row['checks']):
        row['retention_status'] = 'paired-partition-retained'
        row['evidence_level'] = 'source-instance-partition-and-values'
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--raw', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    path = args.source_root / 'tools/iss/run_native_iss_suite.py'
    spec = importlib.util.spec_from_file_location('paired_native_iss_fixture', path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    args.output.mkdir(parents=True, exist_ok=False)
    report = {'measurement_run_sha256': sha(args.raw / 'run-provenance.json'),
              'script_sha256': sha(Path(__file__)), 'fixture_harness_sha256': sha(path), 'rows': []}
    for record in sorted((args.raw / 'iss-supplement/cases').glob('*/result.json')):
        try:
            row = review_case(record.parent, args.output / record.parent.name, helper)
        except (ValueError, OSError, subprocess.TimeoutExpired) as error:
            raw = json.loads(record.read_text())
            row = {'id': raw['id'], 'cohort': 'iss-supplement', 'effect': 'iss',
                   'source_sha256': raw['source_sha256'], 'retention_status': 'measurement-error', 'error': str(error)}
        report['rows'].append(row)
        (args.output / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
        print(row['id'], row['retention_status'], flush=True)


if __name__ == '__main__':
    main()
