"""Classify compiler failures and recognize loop-free experiment inputs."""
import hashlib
from pathlib import Path
import re


TARGETS = {'affine': 'affine', 'rectangular': 'rectangular_tiling',
           'two-level': 'two_level_tiling', 'parallel': 'parallelization',
           'diamond': 'diamond_tiling', 'iss': 'iss'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record(path):
    return {'file': str(path), 'sha256': digest(path)}


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


def source_without_loop(raw, source_root, source_path=None):
    if (source_root is None and source_path is None) or raw['configuration'] not in TARGETS:
        return None
    source = Path(source_path) if source_path is not None else source_root / raw['source_relative']
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
