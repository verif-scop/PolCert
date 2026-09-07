#!/usr/bin/env python3
"""Reuse reviewed effects only after matching complete paired outputs."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

TARGETS = {'affine': 'affine', 'rectangular': 'rectangular_tiling',
           'two-level': 'two_level_tiling', 'parallel': 'parallelization',
           'diamond': 'diamond_tiling', 'iss': 'iss'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record(path):
    return {'file': str(path), 'sha256': digest(path)}


def final_loop(path):
    text = path.read_text(errors='replace')
    marker = '== Optimized Loop =='
    return text.split(marker, 1)[1].strip() if marker in text else None


def output_hashes(case, pattern):
    return sorted({digest(path) for path in (case / 'pluto').glob(pattern)})


def same_experiment(before, after):
    return all(before.get(key) == after.get(key)
               for key in ('id', 'source_sha256', 'polopt_args', 'pluto_args'))


def compatible_pair(old, new):
    before = json.loads((old / 'result.json').read_text())
    after = json.loads((new / 'result.json').read_text())
    if not same_experiment(before, after):
        return False, 'different-input-or-flags'
    if before['timed_out'] or after['timed_out']:
        return False, 'compilation-timeout'
    if any(event for case in (old, new) for event in case.glob('producer-resource-*.json')):
        return False, 'external-producer-resource-limit'
    if before['returncode'] or after['returncode']:
        return False, 'nonzero-exit-needs-stage-review'
    left, right = final_loop(old / 'polcert.stdout.txt'), final_loop(new / 'polcert.stdout.txt')
    if not left or not right:
        return False, 'missing-final-loop'
    if left != right:
        return False, 'different-final-loop'
    old_outputs = output_hashes(old, '*/output.pluto.c')
    new_outputs = output_hashes(new, '*/output.pluto.c')
    if not old_outputs or not new_outputs:
        return False, 'missing-producer-output'
    if any(path.stat().st_size == 0 for case in (old, new)
           for path in (case / 'pluto').glob('*/output.pluto.c')):
        return False, 'empty-producer-output'
    if old_outputs != new_outputs:
        return False, 'different-producer-output'
    return True, 'identical-final-loop-and-producer-c'


def failure_stage(raw, stderr):
    if raw['timed_out']:
        return 'compilation-timeout'
    if raw['returncode'] == 0:
        return None
    if '[tiling-validation] route=rejected' in stderr:
        return 'verified-tiling-rejection'
    if 'Post-tiling affine validation failed' in stderr:
        return 'post-tiling-affine-rejection'
    if '[parallel-validation] status=rejected' in stderr:
        return 'parallel-request-rejection-needs-cause'
    if 'cannot extract tiling witness' in stderr:
        return 'tiling-reader-rejection'
    if 'Affine validation failed' in stderr:
        return 'affine-rejection'
    return 'compilation-failure-needs-cause'


def source_without_loop(raw, source_root):
    if source_root is None or raw['configuration'] not in TARGETS:
        return None
    source = source_root / raw['source_relative']
    if not source.exists() or digest(source) != raw['source_sha256']:
        return None
    text = source.read_text()
    if re.search(r'(?m)^\s*(?:parallel\s+)?for\s', text):
        return None
    # Narrowly recognize straight-line assignments, not arbitrary parser errors.
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if not lines or not all(re.fullmatch(r'[A-Za-z_]\w*(?:\[[^\]]+\])*\s*=\s*[^;]+;', line)
                            for line in lines):
        return None
    return record(source)


def review(root, references, source_root=None, fresh_producers=False):
    planned = json.loads((root / 'manifest.json').read_text())['cases']
    rows = []
    for path in sorted((root / 'cases').glob('*/result.json')):
        raw = json.loads(path.read_text())
        case = path.parent
        stderr = (case / 'polcert.stderr.txt').read_text(errors='replace')
        row = {'id': raw['id'], 'configuration': raw['configuration'],
               'source_sha256': raw['source_sha256'], 'returncode': raw['returncode'],
               'timed_out': raw['timed_out'], 'failure_stage': failure_stage(raw, stderr),
               'tiling_routes': re.findall(r'\[tiling-validation\] route=(\S+)', stderr),
               'parallel_diagnostics': [line for line in stderr.splitlines() if '[parallel-validation]' in line],
               'result': record(path), 'evidence_status': 'requires-new-effect-review',
               'checked_references': []}
        resource_events = [json.loads(event.read_text()) for event in case.glob('producer-resource-*.json')]
        if resource_events:
            row['external_producer_events'] = resource_events
            row['baseline_status'] = 'external-producer-resource-limit'
        for old_root, review_path, old_rows in references:
            prior = old_rows.get(raw['id'])
            old = old_root / 'cases' / raw['id']
            if prior is None or not (old / 'result.json').exists():
                continue
            matches, reason = compatible_pair(old, case)
            row['checked_references'].append({'collection': str(old_root), 'match': matches, 'reason': reason})
            if not matches:
                continue
            row.update({'evidence_status': 'identical-pair-evidence-reused',
                        'producer_status': prior['producer_status'],
                        'retention_status': prior['retention_status'],
                        'prior_review': record(review_path), 'prior_case_evidence': prior,
                        'old_result': record(old / 'result.json'),
                        'final_loop_sha256': hashlib.sha256(final_loop(case / 'polcert.stdout.txt').encode()).hexdigest(),
                        'producer_c_sha256': output_hashes(case, '*/output.pluto.c')})
            break
        if row['evidence_status'] == 'requires-new-effect-review':
            straight_line = source_without_loop(raw, source_root)
            if straight_line is not None:
                row.update({'evidence_status': 'source-structurally-inapplicable',
                            'producer_status': 'absent', 'retention_status': 'not-applicable',
                            'source_evidence': straight_line,
                            'reason': 'The complete source consists of straight-line assignments. '
                                      'There is no source loop to schedule, split, tile or parallelize. '
                                      'The raw requested-route failure, if any, remains recorded.'})
            elif fresh_producers and raw['returncode'] == 0 and not raw['timed_out'] and not resource_events:
                from retention_scop import analyze_producer
                producer = analyze_producer(case)
                target = TARGETS.get(raw['configuration'])
                evidence = case / 'producer-replay-analysis.json'
                evidence.write_text(json.dumps(producer, indent=2) + '\n')
                row['fresh_producer_evidence'] = record(evidence)
                row['producer_analyzer'] = record(Path(analyze_producer.__code__.co_filename).resolve())
                if target and not producer['errors'] and producer['effects'][target]['status'] == 'absent':
                    row.update({'evidence_status': 'fresh-producer-target-absent',
                                'producer_status': 'absent', 'retention_status': 'not-applicable',
                                'reason': 'Completed actual producer outputs contain no nontrivial '
                                          'effect of this configuration target. Other effects are '
                                          'reported separately in the producer analysis.'})
        rows.append(row)
    return {
        'review_script': record(Path(__file__).resolve()),
        'source_mirror': str(source_root) if source_root else None,
        'method': 'Each experiment is rerun. Previous bounded/static effect evidence is reused only '
                  'when input hash, flags, successful termination, complete final Loop, and the set '
                  'of actual producer C bytes match. Compilation success alone establishes no effect. '
                  'Failure stages and producer legality require separate evidence.',
        'planned': len(planned), 'completed': len(rows),
        'counts': dict(Counter(row['evidence_status'] for row in rows)),
        'failure_stages': dict(Counter(row['failure_stage'] for row in rows if row['failure_stage'])),
        'rows': rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--reference', nargs=2, type=Path, action='append', default=[],
                        metavar=('COLLECTION', 'REVIEW'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-root', type=Path,
                        help='Optional source mirror, verified against each frozen input hash')
    parser.add_argument('--fresh-producers', action='store_true',
                        help='Reanalyze actual producer effects of successful unmatched outputs')
    args = parser.parse_args()
    references = []
    for collection, path in args.reference:
        data = json.loads(path.read_text())
        rows = data.get('cases', data.get('rows', []))
        selected = {row['id']: row for row in rows
                    if 'id' in row and 'producer_status' in row and 'retention_status' in row}
        if not selected:
            raise ValueError('No reviewed case evidence: ' + str(path))
        references.append((collection, path, selected))
    result = review(args.root, references, args.source_root, args.fresh_producers)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix('.pending.json')
    temporary.write_text(json.dumps(result, indent=2) + '\n')
    temporary.replace(args.output)
    print(json.dumps({k: result[k] for k in ('planned', 'completed', 'counts', 'failure_stages')}))


if __name__ == '__main__':
    main()
