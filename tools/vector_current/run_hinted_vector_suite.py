#!/usr/bin/env python3
"""Check real vector hints, final innermost effects, and C-sidecar independence."""
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
import json,os,pathlib,subprocess,sys,time
args=sys.argv[1:]
if not args or not pathlib.Path(args[-1]).is_file():
    raise SystemExit(subprocess.call([os.environ['VECTOR_REAL_PLUTO'],*args]))
source=pathlib.Path(args[-1])
out=pathlib.Path(os.environ['VECTOR_CAPTURE'])/str(time.time_ns())
out.mkdir(parents=True); (out/'input.scop').write_bytes(source.read_bytes())
run=subprocess.run([os.environ['VECTOR_REAL_PLUTO'],*args],capture_output=True)
(out/'stdout.txt').write_bytes(run.stdout); (out/'stderr.txt').write_bytes(run.stderr)
for stage in ('beforescheduling','midtransform','posttile','afterscheduling'):
    path=pathlib.Path(str(source)+'.'+stage+'.scop')
    if path.exists(): (out/('output.'+stage+'.scop')).write_bytes(path.read_bytes())
sidecar=pathlib.Path(str(source)+'.pluto.c'); mode=os.environ['VECTOR_SIDECAR']
existed=sidecar.exists()
if mode=='missing' and existed: sidecar.unlink()
if mode=='misleading':
    sidecar.write_text('for (t4=0;t4<1;++t4) { S1(); }\n')
(out/'invocation.json').write_text(json.dumps({'args':args,'returncode':run.returncode,
    'sidecar_mode':mode,'sidecar_existed_before':existed},indent=2)+'\n')
sys.stdout.buffer.write(run.stdout); sys.stderr.buffer.write(run.stderr)
raise SystemExit(run.returncode)
'''


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_loop(text: str) -> dict:
    stack = []
    vectors = []
    assignment_vectors = []
    max_depth = 0
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if line == '}':
            if not stack:
                raise ValueError('unbalanced final loop')
            stack.pop()
            continue
        loop = re.fullmatch(r'(vector |innermost parallel |parallel )?for (\w+) in range\((.*)\) \{', line)
        if loop:
            if any(block.get('vector') for block in stack):
                raise ValueError('vector annotation encloses another loop')
            entry = {'var': loop[2], 'vector': loop[1] in ('vector ', 'innermost parallel '),
                     'bounds': loop[3], 'line': number}
            stack.append(entry)
            depth = sum('var' in block for block in stack)
            max_depth = max(max_depth, depth)
            if entry['vector']:
                vectors.append(dict(entry, depth=depth))
        elif line.endswith('{'):
            stack.append({})
        elif re.match(r'A\[.*=', line):
            active = [block['var'] for block in stack if block.get('vector')]
            assignment_vectors.append(active)
    if stack:
        raise ValueError('unclosed final loop')
    return {'vectors': vectors, 'max_loop_depth': max_depth,
            'assignment_vectors': assignment_vectors}


def positive_four_coordinate_hint(path: Path) -> bool:
    text = path.read_text()
    if not re.search(r'<loop>.*?\bt4\b.*?</loop>', text, re.S):
        return False
    payload = text.split('SCATTERING\n', 1)[1]
    lines = [line.split('#', 1)[0].strip() for line in payload.splitlines()]
    lines = [line for line in lines if line]
    meta = list(map(int, lines[0].split()))
    if meta != [4, 10, 4, 4, 0, 0]:
        return False
    rows = [list(map(int, line.split())) for line in lines[1:5]]
    expected = []
    for dim in range(4):
        row = [0] * 10
        row[1 + dim], row[5 + dim] = -1, 1
        expected.append(row)
    return rows == expected


def numerical_harness(loop: str, shape: dict, matrix: bool) -> str:
    vectors = {entry['var'] for entry in shape['vectors']}
    if len(vectors) != 1 or not shape['assignment_vectors'] or any(
            len(active) != 1 for active in shape['assignment_vectors']):
        raise ValueError('every tested assignment must have one innermost vector annotation')
    vector = next(iter(vectors))
    generated = []
    sites = 0
    for line in transpile_loop_text(loop).splitlines():
        assignment = re.match(r'\s*A\[([^\]]+)\](?:\[([^\]]+)\])?\s*=', line)
        if assignment:
            if bool(assignment[2]) != matrix:
                raise ValueError('unexpected array rank in final output')
            coords = f'{assignment[1]}, {assignment[2]}' if matrix else assignment[1]
            generated.append(f'record({coords}, {vector});')
            sites += 1
        generated.append(line)
    if not sites:
        raise ValueError('no instrumented writes')
    prefix = '#include <stdio.h>\n#include <stdlib.h>\n#include <limits.h>\n#define min(a,b) ((a)<(b)?(a):(b))\n#define max(a,b) ((a)>(b)?(a):(b))\n'
    if matrix:
        data = r'''
static long long A[300][300], B[300][300], count[300][300];
static int current_n,current_m;
static void record(long long i,long long j,long long lane) {
  if(i<0||i>=current_n||j<0||j>=current_m||j!=lane) exit(10);
  count[i][j]++;
}
'''
        main = r'''
int main(void) {
  int sizes[][2]={{0,4},{1,1},{3,5},{31,33},{33,31},{65,4},{4,257},{259,33}};
  for(int s=0;s<8;s++) {
    int N=sizes[s][0],M=sizes[s][1];current_n=N;current_m=M;
    for(int i=0;i<N;i++)for(int j=0;j<M;j++){B[i][j]=17*i-3*j;A[i][j]=0;count[i][j]=0;}
    optimized(N,M);
    for(int i=0;i<N;i++)for(int j=0;j<M;j++)if(A[i][j]!=B[i][j]+1||count[i][j]!=1)return 11;
  }
  puts("complete_samples=8 writes_once=true final_values=true vector_coordinate_is_j=true");
  return 0;
}
'''
        declaration = 'static void optimized(long long N,long long M)'
    else:
        data = r'''
static long long A[400],count[400];
static void record(long long index,long long lane) {
  if(index<0||index>=400||lane<0||lane>=4||index%4!=lane) exit(10);
  count[index]++;
}
'''
        main = r'''
int main(void) {
  for(int i=0;i<400;i++)A[i]=i-200;
  optimized();
  for(int i=0;i<400;i++)if(A[i]!=2*(i-200)+2||count[i]!=1)return 11;
  puts("complete_instances=400 writes_once=true final_values=true vector_coordinate_is_j=true");
  return 0;
}
'''
        declaration = 'static void optimized(void)'
    return prefix + data + INTEGER_HELPERS_C + '\n' + declaration + '{\n' + '\n'.join(generated) + '\n}\n' + main


def run_suite(polopt: Path, pluto: Path, output: Path) -> int:
    output.mkdir(parents=True, exist_ok=False)
    wrapper = output / 'producer-wrapper'
    wrapper.write_text(WRAPPER)
    wrapper.chmod(0o700)
    cases = [
        ('positive-default', 'tools/parallel_current/fixtures/positive.loop', [], False),
        ('positive-notile', 'tools/parallel_current/fixtures/positive.loop', ['--notile'], False),
        ('symbolic-identity', 'tools/second_level_tiling/fixtures/symbolic-independent-2d.loop', ['--identity-tiled'], True),
        ('symbolic-two-level', 'tools/second_level_tiling/fixtures/symbolic-independent-2d.loop', ['--second-level-tile'], True),
        ('dependent-notile', 'tools/parallel_current/fixtures/dependent.loop', ['--notile'], False),
    ]
    rows = []
    for name, relative, extra, matrix in cases:
        modes = ['original', 'missing', 'misleading'] if name == 'positive-default' else ['original']
        reference_loop = None
        for mode in modes:
            case = output / (name + '--' + mode)
            case.mkdir()
            row = {'case': name, 'sidecar': mode, 'source_sha256': sha(ROOT / relative)}
            env = dict(os.environ, COMPCERT_CONFIG=str(ROOT / 'tests/pluto/polcert.ini'),
                       POLCERT_PLUTO=str(wrapper), VECTOR_REAL_PLUTO=str(pluto),
                       VECTOR_CAPTURE=str(case / 'producer'), VECTOR_SIDECAR=mode)
            command = [str(polopt), '--pluto-compat', '--prevector', '--nointratileopt',
                       '--smartfuse', '--nounrolljam', '--noparallel', '--nodiamond-tile',
                       *extra, str(ROOT / relative)]
            row['command'] = command
            try:
                run = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True, timeout=180)
                (case / 'stdout.txt').write_text(run.stdout)
                (case / 'stderr.txt').write_text(run.stderr)
                row['returncode'] = run.returncode
                if run.returncode or '== Optimized Loop ==' not in run.stdout:
                    raise ValueError('no successful final loop')
                final = extract_optimized_loop(run.stdout)
                (case / 'optimized.loop').write_text(final)
                row['loop_sha256'] = sha(case / 'optimized.loop')
                shape = inspect_loop(final)
                row['shape'] = shape
                if name == 'dependent-notile':
                    if shape['vectors'] or '[vector-validation] status=skipped reason=no-hint' not in run.stderr:
                        raise ValueError('dependent no-hint input unexpectedly vectorized')
                else:
                    if not shape['vectors'] or '[vector-validation] status=applied' not in run.stderr:
                        raise ValueError('actual hinted vector effect was not applied')
                    if name == 'positive-default':
                        proposals = list((case / 'producer').glob('*/output.afterscheduling.scop'))
                        if not any(positive_four_coordinate_hint(path) for path in proposals):
                            raise ValueError('the intended four-coordinate t4 proposal was not observed')
                        if shape['max_loop_depth'] != 3:
                            raise ValueError('singleton tile loop was not removed')
                        row['four_schedule_coordinates_three_final_loops'] = True
                    (case / 'check.c').write_text(numerical_harness(final, shape, matrix))
                    build = subprocess.run(['cc', '-O0', '-std=c99', str(case / 'check.c'), '-o', str(case / 'check')], capture_output=True, text=True, timeout=30)
                    (case / 'cc.stderr.txt').write_text(build.stderr)
                    if build.returncode:
                        raise ValueError('numerical/coordinate harness failed to compile')
                    check = subprocess.run([str(case / 'check')], capture_output=True, text=True, timeout=30)
                    (case / 'check.stdout.txt').write_text(check.stdout)
                    (case / 'check.stderr.txt').write_text(check.stderr)
                    if check.returncode:
                        raise ValueError('numerical values, access coverage, or vector coordinate mismatch')
                    row['numerical_and_vector_coordinate_check'] = True
                if reference_loop is None:
                    reference_loop = final
                elif final != reference_loop:
                    raise ValueError('C sidecar changed final vector output')
                row['passed'] = True
            except (OSError, ValueError, subprocess.TimeoutExpired) as error:
                row.update(passed=False, reason=str(error))
            rows.append(row)
            print(json.dumps({key: row[key] for key in ('case', 'sidecar', 'passed', 'reason') if key in row}), flush=True)
            (output / 'summary.json').write_text(json.dumps({
                'binary_sha256': sha(polopt), 'producer_sha256': sha(pluto),
                'script_sha256': sha(Path(__file__)), 'rows': rows}, indent=2) + '\n')
    return 0 if all(row['passed'] for row in rows) else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--polopt', type=Path, default=ROOT / 'polopt')
    parser.add_argument('--pluto', type=Path, default=Path(os.environ.get('POLCERT_PLUTO', '/pluto/tool/pluto')))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix='polcert-vector-hinted-')) / 'results'
    return run_suite(args.polopt.resolve(), args.pluto.resolve(), output.resolve())


if __name__ == '__main__':
    raise SystemExit(main())
