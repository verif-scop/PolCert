"""Select captured producer evidence without guessing which attempt was used.

An unambiguous capture identity or an explicit hash-pinned selection establishes
which baseline is measured. Neither establishes that the compiler consumed it.
"""
import hashlib
import json
from pathlib import Path
import re
from retention_baseline import producer_case_root, validate_baseline


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def select_candidate(case, *, parallel_only=False, explicit=None, expected_sha256=None):
    case = Path(case)
    selected_root = producer_case_root(case)
    root = (selected_root / 'pluto').resolve()
    captures = sorted((selected_root / 'pluto').glob('*/output.pluto.c'))
    result = {'status': 'no-producer-candidate', 'selected': None, 'candidates': [],
              'selection_proves_consumption': False}
    candidates = []
    try:
        protocol = validate_baseline(case)
        if protocol is not None:
            result['baseline_protocol'] = protocol
            result['comparison_basis'] = 'independent-source-and-requested-configuration'
        for path in captures:
            resolved = path.resolve()
            if resolved.parent.parent != root:
                raise ValueError('capture escapes its case directory: ' + str(path))
            if parallel_only and not re.search(r'^\s*#pragma\s+omp\s+parallel\s+for\b',
                                               path.read_text(errors='replace'), re.MULTILINE):
                continue
            folder = path.parent
            invocation_path, input_path = folder / 'invocation.json', folder / 'input.scop'
            invocation = json.loads(invocation_path.read_text())
            argv = invocation.get('argv')
            if (invocation.get('returncode') != 0 or not isinstance(argv, list)
                    or not argv or not all(isinstance(a, str) for a in argv)
                    or not invocation.get('input') or not path.stat().st_size):
                raise ValueError('incomplete or failed producer capture: ' + str(folder))
            normalized_args = ['<captured-input>' if arg == invocation['input'] else arg for arg in argv]
            stages = {p.name: digest(p) for p in sorted(folder.glob('output.*.scop'))}
            identity = {'input_sha256': digest(input_path), 'argv': normalized_args,
                        'producer_c_sha256': digest(path), 'stage_sha256': stages}
            candidate = {'file': str(resolved), 'sha256': digest(path), 'identity': identity,
                         'invocation': str(invocation_path),
                         'invocation_sha256': digest(invocation_path)}
            candidates.append(candidate)
    except (OSError, ValueError, TypeError, KeyError) as error:
        return {**result, 'status': 'unpaired-invalid-capture', 'reason': str(error),
                'candidates': candidates}
    result['candidates'] = candidates
    if explicit is not None:
        if not expected_sha256:
            return {**result, 'status': 'unpaired-missing-explicit-hash'}
        resolved = str(Path(explicit).resolve())
        matches = [candidate for candidate in candidates if candidate['file'] == resolved]
        if len(matches) != 1 or matches[0]['sha256'] != expected_sha256:
            return {**result, 'status': 'unpaired-explicit-capture-mismatch'}
        return {**result, 'status': 'selected', 'selected': matches[0],
                'selection_method': 'explicit-case-capture-and-hash'}
    if not candidates:
        return result
    identities = {json.dumps(candidate['identity'], sort_keys=True) for candidate in candidates}
    if len(identities) != 1:
        return {**result, 'status': 'unpaired-ambiguous-producer-candidates',
                'distinct_identities': len(identities)}
    return {**result, 'status': 'selected', 'selected': candidates[0],
            'selection_method': 'unique-input-flags-output-identity',
            'equivalent_captures': len(candidates)}
