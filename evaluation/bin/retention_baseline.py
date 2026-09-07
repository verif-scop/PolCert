"""An independent Pluto baseline over the strengthened source export.

This compares requested optimization configurations. It does not identify a
proposal consumed by PolCert. Internal optimizer captures remain diagnostic.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def baseline_flags(requested):
    if any(flag in requested for flag in ['--dumpscop', '--readscop', '--moredebug']):
        raise ValueError('Manifest must separate optimization flags from baseline diagnostics')
    # ISS debug output supplies its cuts; --iss --dumpscop is an upstream
    # code-generation failure. No requested optimization flag is removed.
    diagnostics = ['--moredebug'] if '--iss' in requested else ['--dumpscop']
    return ['--readscop', *diagnostics, *requested]


def run_saved(command, cwd, env, prefix, timeout):
    start = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
    prefix.with_suffix('.stdout.txt').write_bytes(stdout)
    prefix.with_suffix('.stderr.txt').write_bytes(stderr)
    result = {'command': command, 'cwd': str(cwd), 'returncode': process.returncode,
              'timed_out': timed_out, 'wall_seconds': time.monotonic() - start}
    dump(prefix.with_suffix('.json'), result)
    return result, stdout


def collect_baseline(case, row, polopt, pluto, wrapper, env, timeout):
    root = case / 'baseline'
    root.mkdir(exist_ok=False)
    work = case / 'work' / 'independent-baseline'
    work.mkdir(parents=True, exist_ok=False)
    protocol = {'schema_version': 1, 'mode': 'independent-strengthened-source',
                'status': 'pending', 'case_id': row['id'], 'source_sha256': row['source_sha256'],
                'requested_pluto_args': row['pluto_args'], 'polopt_sha256': digest(polopt),
                'pluto': str(pluto), 'pluto_sha256': digest(pluto), 'selection_proves_consumption': False,
                'producer_timeout_seconds': timeout,
                'diagnostics': 'ISS uses --moredebug without --dumpscop; other optimization flags are unchanged.'}
    dump(root / 'protocol.json', protocol)
    command = [str(polopt), '--extract-strengthened-only', row['loop_input']]
    extraction, exported = run_saved(command, work, env, root / 'extraction', min(timeout, 60))
    protocol['extraction'] = extraction
    if extraction['returncode'] or extraction['timed_out'] or b'<OpenScop>' not in exported:
        protocol['status'] = 'source-export-failed'
        dump(root / 'protocol.json', protocol)
        return protocol
    source = work / 'source.scop'
    source.write_bytes(exported)
    protocol['input_sha256'] = digest(source)
    producer_env = {**env, 'RETENTION_CAPTURE_DIR': str(root / 'pluto')}
    command = [str(wrapper), *baseline_flags(row['pluto_args']), str(source)]
    producer, _ = run_saved(command, work, producer_env, root / 'producer', timeout)
    protocol['producer'] = producer
    captures = sorted((root / 'pluto').glob('*/invocation.json'))
    protocol['capture_count'] = len(captures)
    protocol['status'] = ('producer-timeout' if producer['timed_out'] else
                          'producer-failed' if producer['returncode'] else
                          'complete' if len(captures) == 1 else 'invalid-capture-count')
    if len(captures) == 1:
        folder = captures[0].parent
        if protocol['status'] == 'complete' and not (folder / 'output.pluto.c').is_file():
            protocol['status'] = 'producer-output-missing'
        protocol['capture'] = str(folder.relative_to(root))
        protocol['files_sha256'] = {str(p.relative_to(root)): digest(p)
                                    for p in sorted(folder.iterdir()) if p.is_file()}
    dump(root / 'protocol.json', protocol)
    return protocol


def producer_case_root(case):
    case = Path(case)
    return case / 'baseline' if (case / 'baseline').exists() else case


def validate_baseline(case):
    """Validate an explicit baseline; never fall back to internal captures."""
    case = Path(case)
    root = case / 'baseline'
    if not root.exists():
        return None
    protocol = json.loads((root / 'protocol.json').read_text())
    raw = json.loads((case / 'result.json').read_text())
    if protocol.get('schema_version') != 1 or protocol.get('mode') != 'independent-strengthened-source':
        raise ValueError('Unsupported independent baseline protocol')
    for key, expected in [('case_id', raw['id']), ('source_sha256', raw['source_sha256']),
                          ('requested_pluto_args', raw['pluto_args'])]:
        if protocol.get(key) != expected:
            raise ValueError('Independent baseline mismatch: ' + key)
    if protocol.get('status') != 'complete':
        raise ValueError('Independent baseline is not complete: ' + str(protocol.get('status')))
    capture = (root / protocol['capture']).resolve()
    if capture.parent != (root / 'pluto').resolve():
        raise ValueError('Independent baseline capture escapes its root')
    if sorted(p.resolve() for p in (root / 'pluto').glob('*/invocation.json')) != [capture / 'invocation.json']:
        raise ValueError('Independent baseline must contain exactly its declared invocation')
    files = protocol.get('files_sha256', {})
    if not files:
        raise ValueError('Independent baseline has no file identities')
    actual_files = {str(p.relative_to(root.resolve())) for p in capture.iterdir() if p.is_file()}
    if set(files) != actual_files:
        raise ValueError('Independent baseline file inventory changed')
    for relative, expected in files.items():
        path = (root / relative).resolve()
        if path.parent != capture or digest(path) != expected:
            raise ValueError('Independent baseline file mismatch: ' + relative)
    for name in ['input.scop', 'invocation.json', 'output.pluto.c']:
        path = capture / name
        if str(path.relative_to(root.resolve())) not in files or not path.stat().st_size:
            raise ValueError('Independent baseline missing required evidence: ' + name)
    if digest(capture / 'input.scop') != protocol['input_sha256']:
        raise ValueError('Independent baseline source export mismatch')
    invocation = json.loads((capture / 'invocation.json').read_text())
    expected_args = baseline_flags(raw['pluto_args'])
    if invocation['argv'][1:-1] != expected_args:
        raise ValueError('Independent baseline invocation flags mismatch')
    if invocation['returncode'] != 0:
        raise ValueError('Independent baseline producer did not succeed')
    if invocation['argv'][0] != protocol['pluto']:
        raise ValueError('Independent baseline producer executable mismatch')
    for key in ['polopt_sha256', 'pluto_sha256']:
        if protocol[key] != raw[key]:
            raise ValueError('Independent baseline binary provenance mismatch: ' + key)
    return protocol
