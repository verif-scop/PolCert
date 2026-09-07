#!/usr/bin/env python3
"""Check the read-only export against the native affine scheduler's input."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--identity-producer':
        source = next(Path(a) for a in sys.argv[2:] if a.endswith('.scop'))
        captured = Path(os.environ['EXPORT_CHECK_CAPTURE']) / (str(time.time_ns()) + '.scop')
        shutil.copy2(source, captured)
        shutil.copy2(source, str(source) + '.afterscheduling.scop')
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--polopt', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--input', action='append', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    wrapper = args.output / 'identity-producer'
    wrapper.write_text('#!/usr/bin/env python3\nimport os, sys\nos.execv(sys.executable, '
                       + repr([sys.executable, str(Path(__file__).resolve()), '--identity-producer'])
                       + ' + sys.argv[1:])\n')
    wrapper.chmod(0o755)
    inputs = args.input or [args.source_root / 'tests/polopt-generated/inputs' / (name + '.loop')
                            for name in ['nodep', 'negparam', 'multi-loop-param']]
    rows = []
    for source in inputs:
        target = args.output / source.stem
        target.mkdir()
        captures = target / 'captures'
        captures.mkdir()
        env = {**os.environ, 'POLCERT_PLUTO': str(wrapper.resolve()),
               'EXPORT_CHECK_CAPTURE': str(captures.resolve()),
               'COMPCERT_CONFIG': str(args.source_root / 'tests/pluto/polcert.ini')}
        def run(label, flags):
            command = [str(args.polopt), *flags, str(source)]
            result = subprocess.run(command, cwd=target, env=env, capture_output=True, timeout=60)
            (target / (label + '.stdout.txt')).write_bytes(result.stdout)
            (target / (label + '.stderr.txt')).write_bytes(result.stderr)
            return {'command': command, 'returncode': result.returncode,
                    'stdout_sha256': hashlib.sha256(result.stdout).hexdigest()}, result.stdout
        strengthened, exported = run('strengthened', ['--extract-strengthened-only'])
        no_calls = not list(captures.iterdir())
        raw, raw_text = run('raw', ['--extract-only'])
        raw_repeat, raw_again = run('raw-repeat', ['--extract-only'])
        no_calls = no_calls and not list(captures.iterdir())
        native, _ = run('native', ['--notile'])
        captured_inputs = list(captures.glob('*.scop'))
        byte_equal = bool(captured_inputs) and all(p.read_bytes() == exported for p in captured_inputs)
        # stdout mode appends print_newline after the same OpenScop printer.
        # Permit exactly that final LF, not whitespace normalization of rows.
        matches = bool(captured_inputs) and all(exported in (p.read_bytes(), p.read_bytes() + b'\n')
                                                 for p in captured_inputs)
        invalid, _ = run('invalid', ['--extract-only', '--extract-strengthened-only'])
        row = {'source': str(source), 'source_sha256': sha(source), 'strengthened': strengthened,
               'raw': raw, 'raw_repeat': raw_repeat, 'native': native, 'invalid': invalid,
               'no_producer_calls_during_export': no_calls, 'raw_export_stable': raw_text == raw_again,
               'native_input_byte_equal': byte_equal,
               'native_input_equal_except_single_stdout_lf': matches,
               'captured_inputs': {str(p): sha(p) for p in captured_inputs}}
        row['passed'] = (all(r['returncode'] == 0 for r in [strengthened, raw, raw_repeat, native])
                         and invalid['returncode'] != 0 and no_calls and matches and raw_text == raw_again)
        rows.append(row)
    report = {'polopt': str(args.polopt), 'polopt_sha256': sha(args.polopt),
              'script_sha256': sha(Path(__file__)), 'rows': rows, 'passed': all(r['passed'] for r in rows)}
    (args.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
