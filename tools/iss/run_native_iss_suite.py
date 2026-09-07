#!/usr/bin/env python3
"""Require native ISS to preserve its split and feed it to later passes."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/end_to_end_c'))
from loop_to_c import INTEGER_HELPERS_C, transpile_loop_text
from runner_common import extract_optimized_loop


WRAPPER = r'''#!/usr/bin/env python3
import hashlib, json, os, pathlib, subprocess, sys
args = sys.argv[1:]
source = pathlib.Path(args[-1])
content = source.read_bytes()
digest = hashlib.sha256(content).hexdigest()
saved = pathlib.Path(os.environ['ISS_NATIVE_LOG']).parent / ('input-' + digest + '.scop')
saved.write_bytes(content)
record = {'args': args, 'input_statements': content.decode().count('\nDOMAIN\n'),
          'input_sha256': digest, 'saved_input': str(saved)}
result = subprocess.run([os.environ['ISS_REAL_PLUTO'], *args])
record['returncode'] = result.returncode
with open(os.environ['ISS_NATIVE_LOG'], 'a') as output:
    output.write(json.dumps(record) + '\n')
raise SystemExit(result.returncode)
'''


def harness(source: str, optimized: str, rank: int = 1, cut_axis: int = 0) -> tuple[str, int]:
    site_count = 0
    lines = []
    for line in transpile_loop_text(optimized).splitlines():
        match = re.match(r'\s*A\[(.*?)\](?:\[(.*?)\])?\s*=', line)
        if match:
            second = match[2] if rank == 2 else '0'
            lines.append(f'record({site_count}, {match[1]}, {second}, N, M);')
            site_count += 1
        lines.append(line)
    if site_count < 2 or site_count > 256:
        raise ValueError(f'expected split assignment sites, got {site_count}')
    code = r'''
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#define min(a,b) ((a)<(b)?(a):(b))
#define max(a,b) ((a)>(b)?(a):(b))
static long long ARRAY_DECL, expected[1100][1100], count[1100][1100], lo[256], hi[256];
static void record(int site, long long i, long long j, long long N, long long M) {
  if (i < 0 || i >= N || j < 0 || j >= M) exit(11);
  count[i][j]++;
  long long index = CUT_INDEX;
  if (index < lo[site]) lo[site] = index;
  if (index > hi[site]) hi[site] = index;
}
'''.replace('ARRAY_DECL', 'A[1100][1100]' if rank == 2 else 'A[1100]').replace('CUT_INDEX', 'j' if cut_axis else 'i')
    code += INTEGER_HELPERS_C
    code += '\nstatic void original(long long N, long long M) {\n' + transpile_loop_text(source) + '}\n'
    code += '\nstatic void optimized(long long N, long long M) {\n' + '\n'.join(lines) + '\n}\n'
    code += r'''
int main(void) {
  long long sizes[] = {2,31,32,33,63,64,65,257,259,1027};
  for (int sample=0; sample<10; sample++) {
    long long N=N_SIZE, M=M_SIZE, extent=CUT_EXTENT;
    for (int i=0;i<N;i++) for(int j=0;j<M;j++) ARRAY_ACCESS=i*M+j+1;
    original(N,M);
    for (int i=0;i<N;i++) for(int j=0;j<M;j++) { expected[i][j]=ARRAY_ACCESS; ARRAY_ACCESS=i*M+j+1; count[i][j]=0; }
    for (int s=0;s<256;s++) { lo[s]=LLONG_MAX; hi[s]=-1; }
    optimized(N,M);
    for (int i=0;i<N;i++) for(int j=0;j<M;j++) if (ARRAY_ACCESS!=expected[i][j] || count[i][j]!=1) return 12;
    int left=0, right=0;
    for (int s=0;s<SITE_COUNT;s++) if (hi[s]>=0) {
      if (2*hi[s]<extent) left=1;
      else if (2*lo[s]>=extent) right=1;
      else return 13;
    }
    if (!left || !right) return 14;
    printf("N=%lld M=%lld exact_values=true partition_sites=true iterations_once=true\n",N,M);
  }
  return 0;
}
'''.replace('SITE_COUNT', str(site_count)).replace('N_SIZE', '5' if cut_axis else 'sizes[sample]').replace('M_SIZE', 'sizes[sample]' if cut_axis else ('5' if rank == 2 else '1')).replace('CUT_EXTENT', 'M' if cut_axis else 'N').replace('ARRAY_ACCESS', 'A[i][j]' if rank == 2 else 'A[i]')
    return code, site_count


def run_suite(output: Path, polopt: Path, pluto: Path, selected: list[str] | None, kernels: list[str] | None) -> int:
    output.mkdir(parents=True, exist_ok=True)
    wrapper = output / 'pluto-record'
    wrapper.write_text(WRAPPER)
    wrapper.chmod(0o755)
    sources = {
        'reverse': (ROOT / 'tests/end-to-end-c/cases/reverse_iss/reverse_iss.loop', 1, 0),
        'reverse-rows': (ROOT / 'tests/iss-native/reverse_rows.loop', 2, 0),
        'reverse-columns': (ROOT / 'tests/iss-native/reverse_columns.loop', 2, 1),
    }
    if kernels:
        if set(kernels) - set(sources):
            raise ValueError('unknown native ISS kernel')
        sources = {name: sources[name] for name in kernels}
    compatibility = ['--pluto-compat', '--noprevector', '--nounrolljam', '--noparallel', '--nodiamond-tile']
    plain_schedule = compatibility + ['--nointratileopt']
    variants = [
        ('native', ['--iss'], True),
        ('affine', plain_schedule + ['--iss', '--notile'], False),
        ('identity-tiled', plain_schedule + ['--iss', '--identity', '--tile'], True),
        ('two-level', plain_schedule + ['--iss', '--second-level-tile'], True),
        ('post-tiling-affine', compatibility + ['--iss', '--tile', '--intratileopt'], True),
    ]
    if selected:
        if set(selected) - {name for name, _, _ in variants}:
            raise ValueError('unknown native ISS configuration')
        variants = [row for row in variants if row[0] in selected]
    rows = []
    jobs = [(kernel, source, rank, cut_axis, name, flags, tiled)
            for kernel, (source, rank, cut_axis) in sources.items()
            for name, flags, tiled in variants]
    for kernel, source, rank, cut_axis, name, flags, tiled in jobs:
        directory = output / (kernel + '--' + name)
        directory.mkdir(exist_ok=False)
        log = directory / 'pluto.jsonl'
        env = dict(os.environ, COMPCERT_CONFIG=str(ROOT / 'tests/pluto/polcert.ini'),
                   POLCERT_PLUTO=str(wrapper), ISS_REAL_PLUTO=str(pluto), ISS_NATIVE_LOG=str(log))
        command = [str(polopt), *flags, str(source)]
        row = {'kernel': kernel, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
               'configuration': name, 'command': command}
        try:
            compiled = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
            (directory / 'compiler.stdout.txt').write_text(compiled.stdout)
            (directory / 'compiler.stderr.txt').write_text(compiled.stderr)
            row['compiler_returncode'] = compiled.returncode
            if compiled.returncode != 0:
                raise ValueError('native compilation rejected')
            invocations = [json.loads(line) for line in log.read_text().splitlines()]
            row['invocations'] = invocations
            if not any(call['input_statements'] == 2 for call in invocations):
                raise ValueError('checked split did not reach a later optimizer invocation')
            if any('--iss' in call['args'] and '--dumpscop' in call['args'] for call in invocations):
                raise ValueError('later optimizer requested ISS again')
            if any(call['returncode'] != 0 for call in invocations):
                raise ValueError('an optimizer invocation failed')
            optimized = extract_optimized_loop(compiled.stdout)
            (directory / 'optimized.loop').write_text(optimized)
            # Pluto does not tile the one-dimensional reverse kernel.  The
            # two matrix kernels exercise the combined ISS + tiling routes.
            required_sizes = ([8, 32] if name == 'two-level' else [32]) if tiled and rank == 2 else []
            for tile_size in required_sizes:
                if not any('range(' in line and re.search(r'\b' + str(tile_size) + r'\b', line)
                           for line in optimized.splitlines()):
                    raise ValueError(f'no tile-size {tile_size} bound in final loop')
            text, sites = harness(source.read_text(), optimized, rank, cut_axis)
            (directory / 'check.c').write_text(text)
            build = subprocess.run(['cc', '-O0', '-std=c99', str(directory / 'check.c'), '-o', str(directory / 'check')], capture_output=True, text=True)
            (directory / 'cc.stderr.txt').write_text(build.stderr)
            if build.returncode:
                raise ValueError('structural/equality harness did not compile')
            check = subprocess.run([str(directory / 'check')], capture_output=True, text=True, timeout=30)
            (directory / 'check.stdout.txt').write_text(check.stdout)
            if check.returncode:
                raise ValueError(f'final split/equality check failed: {check.returncode}')
            row.update(passed=True, assignment_sites=sites, complete_samples=10,
                       required_tile_sizes=required_sizes)
        except subprocess.TimeoutExpired as error:
            (directory / 'timeout.stdout.txt').write_bytes(error.stdout or b'')
            (directory / 'timeout.stderr.txt').write_bytes(error.stderr or b'')
            row.update(passed=False, reason='timeout', timed_out_command=error.cmd)
        except (ValueError, OSError) as error:
            row.update(passed=False, reason=str(error))
        rows.append(row)
        print(json.dumps({key: row[key] for key in
                          ('kernel', 'configuration', 'passed', 'reason', 'assignment_sites')
                          if key in row}), flush=True)
    provenance = {name: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                  for name, path in [('polopt', polopt), ('pluto', pluto),
                                     ('iss_helper', ROOT / 'tools/iss/pluto_iss_check.py'),
                                     ('runner', Path(__file__))]}
    (output / 'summary.json').write_text(json.dumps({'rows': rows, 'provenance': provenance}, indent=2) + '\n')
    return 0 if all(row['passed'] for row in rows) else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--polopt', type=Path, default=ROOT / 'polopt')
    parser.add_argument('--pluto', type=Path, default=Path(os.environ.get('POLCERT_PLUTO', '/pluto/tool/pluto')))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cases', nargs='+')
    parser.add_argument('--kernels', nargs='+')
    args = parser.parse_args()
    if args.output:
        return run_suite(args.output.resolve(), args.polopt.resolve(), args.pluto.resolve(), args.cases, args.kernels)
    with tempfile.TemporaryDirectory(prefix='polcert-native-iss-') as temporary:
        return run_suite(Path(temporary), args.polopt.resolve(), args.pluto.resolve(), args.cases, args.kernels)


if __name__ == '__main__':
    raise SystemExit(main())
