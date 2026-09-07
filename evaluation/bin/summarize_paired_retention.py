#!/usr/bin/env python3
"""One entry point for fresh paired-effect evidence and source-deduplicated rows."""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

from retention_baseline import validate_baseline


TARGETS = {'affine': 'affine', 'rectangular': 'rectangular_tiling', 'two-level': 'two_level_tiling',
           'diamond': 'diamond_tiling', 'iss': 'iss', 'parallel': 'parallelization'}
PRIMARY = {'affine': ['primary-affine'], 'rectangular_tiling': ['primary-rectangular'],
           'two_level_tiling': ['primary-two-level'], 'diamond_tiling': ['primary-diamond', 'diamond-supplement'],
           'iss': ['primary-iss', 'iss-supplement'], 'parallelization': ['standard-parallel']}
RETAINED = {'sampled-retained', 'sampled-source-instance-retained', 'statically-retained', 'paired-partition-retained'}
UNAVAILABLE_BASELINES = {'producer-timeout', 'producer-failed', 'producer-output-missing',
                         'producer-codegen-failure', 'producer-resource-limit'}


def publication_gate(rows):
    """Keep missing/unknown producers outside neither the gate nor the report.

    A complete capture is not proof of a usable generated program. An explicit
    hash-bound code-generation review may classify an unusable C baseline;
    absent effects and baseline failures are distinct from native failures.
    """
    missing = [r['id'] for r in rows if 'result_sha256' not in r]
    unavailable = [dict(id=r['id'], cohort=r['cohort'], reason=r.get('baseline_status'),
                        detail=r.get('baseline_detail'), evidence=r.get('review_file'))
                   for r in rows if r.get('retention_status') == 'baseline-unavailable']
    unknown = [r['id'] for r in rows
               if r['producer_status'] not in ('observed', 'absent', 'unsafe-producer-output')
               and not (r.get('retention_status') == 'baseline-unavailable'
                        and r.get('baseline_status') in UNAVAILABLE_BASELINES)]
    unresolved = [r['id'] for r in rows if r['producer_status'] == 'observed'
                  and r['retention_status'] not in RETAINED | {'not-retained', 'native-failed', 'native-timeout'}]
    return {'collection_complete': not missing, 'not_collected_ids': missing,
            'producer_unknown_ids': unknown, 'producer_unknown_count': len(unknown),
            'baseline_unavailable': unavailable,
            'baseline_unavailable_by_reason': dict(Counter(r['reason'] for r in unavailable)),
            'observed_unresolved_ids': unresolved, 'observed_unresolved_count': len(unresolved),
            'ready': not missing and not unknown and not unresolved}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_counts(rows):
    observed = defaultdict(list)
    for row in rows:
        if row['producer_status'] == 'observed':
            observed[row['source_sha256']].append(row)
    counts = Counter()
    for source, pairs in observed.items():
        if all(row['retention_status'] in RETAINED for row in pairs):
            counts['retained'] += 1
        elif any(row['retention_status'] in ('not-retained', 'native-failed', 'native-timeout') for row in pairs):
            counts['not_retained'] += 1
        else:
            counts['requires_review'] += 1
    return {'pluto_distinct_sources': len(observed), 'retained_distinct_sources': counts['retained'],
            'not_retained_distinct_sources': counts['not_retained'],
            'requires_review_distinct_sources': counts['requires_review']}


def outcome_details(rows):
    """Expose exclusions and loss causes, independently of the denominator."""
    by_source = defaultdict(list)
    for row in rows:
        by_source[row['source_sha256']].append(row)
    absent, unavailable = [], []
    losses = defaultdict(set)
    for source, pairs in by_source.items():
        if all(r['producer_status'] == 'absent' for r in pairs):
            absent.append(source)
        if all(r['retention_status'] == 'baseline-unavailable' for r in pairs):
            unavailable.append(source)
        for row in pairs:
            if row['producer_status'] == 'observed' and row['retention_status'] in ('not-retained', 'native-failed', 'native-timeout'):
                cause = row.get('classification', row['retention_status'])
                losses[cause].add(source)
    return {'no_effect_distinct_sources': len(absent),
            'baseline_unavailable_distinct_sources': len(unavailable),
            'loss_causes_distinct_sources': {cause: len(sources) for cause, sources in sorted(losses.items())}}


def parallel_observation_matches(row, observed, protocol):
    if observed.get('source_sha256') != row['source_sha256'] or observed.get('final_sha256') != row['final_sha256']:
        return False
    if observed.get('producer_sha256') is not None:
        return observed['producer_sha256'] == row['producer_sha256']
    # A baseline without an OpenMP loop has no selected *parallel* C file.
    # Bind that absence result to the complete, hash-checked baseline instead
    # of treating a missing producer hash as permission to match anything.
    selection = observed.get('producer_selection', {})
    return (observed.get('producer_status') == 'absent' and
            selection.get('status') == 'no-producer-candidate' and
            selection.get('baseline_protocol') == protocol)


def load_override(paths, run_sha):
    rows = {}
    for path in paths:
        report = json.loads(path.read_text())
        if report.get('measurement_run_sha256') != run_sha:
            raise ValueError('Supplementary review is not bound to this fresh measurement run: ' + str(path))
        for row in report['rows']:
            key = row['cohort'], row['id'], row['effect']
            if key in rows:
                raise ValueError('Conflicting supplementary evidence: ' + repr(key))
            rows[key] = {**row, 'review_file': str(path), 'review_sha256': sha(path)}
    return rows


def summarize(args):
    plan = json.loads(args.plan.read_text())
    run_sha = sha(args.raw / 'run-provenance.json')
    if args.reviews.exists():
        review_identity = json.loads((args.reviews / 'review-provenance.json').read_text())
        if review_identity.get('measurement_run_sha256') != run_sha:
            raise ValueError('Reviews belong to a different measurement run')
    overrides = load_override(args.supplement_review, run_sha)
    rows = []
    for collection in plan['collections']:
        cohort = collection['cohort']
        manifest = args.plan.parent / collection['manifest']
        if sha(manifest) != collection['manifest_sha256']:
            raise ValueError('Frozen manifest changed')
        for requested in json.loads(manifest.read_text())['cases']:
            case = args.raw / collection['result_directory'] / 'cases' / requested['id']
            family = 'iss' if requested['configuration'].startswith('iss-') else TARGETS.get(requested['configuration'])
            row = {'cohort': cohort, 'id': requested['id'], 'source_sha256': requested['source_sha256'],
                   'configuration': requested['configuration'], 'effect': family,
                   'producer_status': 'not-measured', 'retention_status': 'not-collected', 'case_directory': str(case)}
            record = case / 'result.json'
            if not record.exists():
                rows.append(row)
                continue
            raw = json.loads(record.read_text())
            if any(raw.get(key) != requested.get(key) for key in ('id', 'source_sha256', 'polopt_args', 'pluto_args')):
                raise ValueError('Collected pair differs from manifest: ' + row['id'])
            if sha(case / 'source.loop') != row['source_sha256']:
                raise ValueError('Archived source changed: ' + row['id'])
            protocol = json.loads((case / 'baseline/protocol.json').read_text())
            row.update(native_returncode=raw['returncode'], native_timeout=raw['timed_out'],
                       baseline_status=protocol['status'], result_sha256=sha(record))
            try:
                validate_baseline(case)
            except (ValueError, OSError) as error:
                row.update(retention_status='baseline-unavailable', baseline_detail=str(error))
                rows.append(row)
                continue
            capture = case / 'baseline' / protocol['capture']
            row.update(producer_sha256=sha(capture / 'output.pluto.c'), final_sha256=sha(case / 'polcert.stdout.txt'))
            analysis_path = args.reviews / cohort / 'cases' / row['id'] / 'effect-analysis.json'
            if analysis_path.exists():
                analysis = json.loads(analysis_path.read_text())
                if analysis.get('source_sha256') != row['source_sha256']:
                    raise ValueError('Effect analysis source mismatch')
                row['all_effects'] = analysis['effects']
                if family:
                    effect = analysis['effects'][family]
                    row.update(producer_status=effect['producer'], retention_status=effect['retention'])
                row['analysis_file'] = str(analysis_path)
                row['analysis_sha256'] = sha(analysis_path)
            else:
                row['retention_status'] = 'not-analyzed'
            parallel = args.reviews / cohort / 'parallel' / row['id'] / row['id'] / 'evidence.json'
            if family == 'parallelization' and parallel.exists():
                observed = json.loads(parallel.read_text())
                if not parallel_observation_matches(row, observed, protocol):
                    raise ValueError('Parallel observation is not paired with these outputs')
                row.update(producer_status=observed['producer_status'], retention_status=observed['retention_status'],
                           evidence_level=observed.get('evidence_level'), membership_evidence=str(parallel))
            override = overrides.get((cohort, row['id'], family))
            if override:
                for key in ('source_sha256', 'producer_sha256', 'final_sha256'):
                    if override.get(key) != row[key]:
                        raise ValueError('Supplementary review output mismatch: ' + key)
                row.update(override)
                if row['retention_status'] == 'baseline-unavailable':
                    # Explicit independent C diagnostics, never native timeout,
                    # can remove a proposal from the comparable-C denominator.
                    if row.get('baseline_status') not in UNAVAILABLE_BASELINES:
                        raise ValueError('Unclassified unavailable baseline: ' + row['id'])
                    row['producer_status'] = 'unavailable'
            if row['producer_status'] == 'observed' and raw['timed_out']:
                row['retention_status'] = 'native-timeout'
            elif row['producer_status'] == 'observed' and raw['returncode']:
                row['retention_status'] = 'native-failed'
            if row['retention_status'] == 'producer-cross-iteration-conflict':
                row['producer_status'] = 'unsafe-producer-output'
            rows.append(row)
    primary = []
    for effect, cohorts in PRIMARY.items():
        selected = [row for row in rows if row['cohort'] in cohorts]
        primary.append({'effect': effect, 'cohorts': cohorts, 'planned_pairs': len(selected),
                        'planned_distinct_sources': len({row['source_sha256'] for row in selected}),
                        **source_counts(selected),
                        **outcome_details(selected),
                        'publication_gate': publication_gate(selected),
                        'pair_statuses': dict(Counter(row['producer_status'] + ':' + row['retention_status'] for row in selected))})
    summary = {'measurement_run_sha256': run_sha, 'plan_sha256': sha(args.plan),
               'planned_pairs': len(rows), 'recorded_pairs': sum('result_sha256' in row for row in rows),
               'primary': primary, 'rows': rows,
               'primary_publication_ready': all(r['publication_gate']['ready'] for r in primary),
               'counting_rule': 'Distinct source hashes. A source is retained only when every observed paired configuration in its reported effect/cohort is retained. Baseline failures, absent effects, and controls do not enter the produced-effect denominator.',
               'limitations': 'Bounded observations are empirical evidence, not all-input equivalence. Access-only matches do not count as source-instance retention. Native failures require stage review; a failed producer is not a validator false positive.'}
    summary['additional_cohorts'] = [
        {'cohort': cohort, 'planned_pairs': len(selected),
         'recorded_pairs': sum('result_sha256' in r for r in selected),
         'pair_statuses': dict(Counter(r['producer_status'] + ':' + r['retention_status'] for r in selected)),
         'all_effects_pair_statuses': {effect: dict(Counter(
             e['producer'] + ':' + e['retention'] for r in selected
             if (e := r.get('all_effects', {}).get(effect)) is not None)) for effect in PRIMARY},
         'scope': 'Supplementary configurations, excluded from the six primary rows; initial per-effect observations are not a claim that every combined effect was retained.'}
        for cohort in ('legacy-innerpar', 'combined')
        if (selected := [r for r in rows if r['cohort'] == cohort])]
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: summary[key] for key in ('planned_pairs', 'recorded_pairs', 'primary')}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--raw', type=Path, required=True)
    parser.add_argument('--reviews', type=Path, required=True)
    parser.add_argument('--supplement-review', type=Path, action='append', default=[])
    parser.add_argument('--output', type=Path, required=True)
    summarize(parser.parse_args())


if __name__ == '__main__':
    main()
