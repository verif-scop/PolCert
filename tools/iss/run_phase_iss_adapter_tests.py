#!/usr/bin/env python3
"""Link ISS adapter tests against an already-built, isolated PolCert tree."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, out = args.source_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = root / 'tools/iss/test_phase_iss_adapter.ml'
    # Compile a copy, keeping build products out of the shared source tree.
    local = out / source.name
    local.write_bytes(source.read_bytes())
    makefile = out / 'adapter-test.mk'
    makefile.write_text(
        'include Makefile.extr\n'
        '.PHONY: iss-adapter-test\n'
        'iss-adapter-test:\n'
        '\t$(OCAMLOPT) -o ' + str(out / 'adapter-test') + ' $(LIBS) '
        '$(shell $(MODORDER) extraction/SPolOpt.cmx syntax/SLoopIss.cmx driver/PhaseISS.cmx) '
        + str(local) + '\n')
    commands = [
        ['make', '-f', str(makefile), 'iss-adapter-test'],
        [str(out / 'adapter-test')],
    ]
    results = []
    env = dict(os.environ, COMPCERT_CONFIG=str(root / 'tests/pluto/polcert.ini'))
    for label, command in zip(['build', 'test'], commands):
        result = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=180)
        (out / (label + '.stdout.txt')).write_bytes(result.stdout)
        (out / (label + '.stderr.txt')).write_bytes(result.stderr)
        results.append({'command': command, 'returncode': result.returncode})
        if result.returncode:
            break
    paths = ['polopt', 'driver/PhaseISS.ml', 'syntax/SLoopMain.ml',
             'tools/iss/test_phase_iss_adapter.ml', 'extraction/ISSBoolChecker.ml']
    summary = {'source_root': str(root), 'results': results,
               'sha256': {path: hashlib.sha256((root/path).read_bytes()).hexdigest()
                          for path in paths},
               'passed': len(results) == 2 and all(x['returncode'] == 0 for x in results)}
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    return 0 if summary['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
