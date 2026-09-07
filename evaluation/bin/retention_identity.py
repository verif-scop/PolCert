"""Sufficient, conservative identity checks for access-membership evidence.

This is an observer audit, not a correctness validator. Full column rank makes
an affine access vector injective for fixed parameters. Distinct access tags
then distinguish statements. Rank deficiency or a shared tag requests a
source-instance/static review; neither establishes a compiler defect.
"""
from collections import defaultdict
from fractions import Fraction
import hashlib
from pathlib import Path

from retention_scop import affine_map, read_scop


def rank(rows, columns):
    matrix = [[Fraction(x) for x in row] for row in rows]
    pivot = 0
    for column in range(columns):
        chosen = next((i for i in range(pivot, len(matrix)) if matrix[i][column]), None)
        if chosen is None:
            continue
        matrix[pivot], matrix[chosen] = matrix[chosen], matrix[pivot]
        divisor = matrix[pivot][column]
        matrix[pivot] = [x / divisor for x in matrix[pivot]]
        for i in range(pivot + 1, len(matrix)):
            factor = matrix[i][column]
            matrix[i] = [x - factor * y for x, y in zip(matrix[i], matrix[pivot])]
        pivot += 1
    return pivot


def audit_scop(path):
    path = Path(path)
    result = {'source_scop': str(path), 'source_scop_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
              'method': 'Distinct read/write object-and-rank tags plus full-column-rank affine access maps at fixed parameters.',
              'statements': [], 'shared_access_tags': [], 'identity_safe': False}
    try:
        source = read_scop(path)
        tags = defaultdict(list)
        for index, statement in enumerate(source.statements, 1):
            depth = statement.domain.outputs
            coefficients, signature = [], []
            for access in statement.accesses:
                if access.inputs != depth:
                    raise ValueError('Source access/domain dimension mismatch')
                mapping = affine_map(access)
                if not mapping or any(mapping[0][:-1]):
                    raise ValueError('Source array identity is not constant')
                obj = mapping[0][-1]
                if obj.denominator != 1:
                    raise ValueError('Nonintegral source array identity')
                signature.append((access.kind, int(obj), access.outputs - 1))
                coefficients.extend(row[:depth] for row in mapping[1:])
            # Sorting deliberately overapproximates tag collisions: different
            # access orders may trigger review, but cannot pass by accident.
            signature = tuple(sorted(signature))
            actual_rank = rank(coefficients, depth)
            row = {'statement': index, 'iteration_dimensions': depth,
                   'access_rank': actual_rank, 'access_tags': signature,
                   'injective_sufficient': bool(signature) and actual_rank == depth}
            result['statements'].append(row)
            tags[signature].append(index)
        result['shared_access_tags'] = [{'statements': ids, 'tags': tag}
                                         for tag, ids in tags.items() if len(ids) > 1]
        result['identity_safe'] = bool(source.statements) and not result['shared_access_tags'] and all(
            row['injective_sufficient'] for row in result['statements'])
        result['status'] = 'access-identifies-source-instance' if result['identity_safe'] else 'requires-source-instance-review'
    except (ValueError, OSError) as error:
        result.update(status='identity-audit-unsupported', error=str(error))
    return result


def supports_instance_identity(audit, observations):
    return audit.get('identity_safe') is True and bool(observations) and all(
        observation[side].get('duplicate_access_records') == 0
        for observation in observations for side in ('pluto', 'polcert'))
