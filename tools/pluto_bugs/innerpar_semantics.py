"""Check complete array states and singleton parallel loops in finite fixtures."""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'end_to_end_c'))
from loop_to_c import INTEGER_HELPERS_C, transpile_line


def optimized_loop(output):
    marker = '== Optimized Loop ==\n'
    if output.count(marker) != 1:
        raise AssertionError('expected exactly one optimized Loop')
    text = output.split(marker, 1)[1]
    # Combined stdout/stderr may put this diagnostic after the printed program.
    return '\n'.join(line for line in text.splitlines()
                     if line.strip() != '[tiling-validation] route=permutable-band')


def render_checked_state(loop, fixture='innerpar'):
    """Count every reached parallel iteration and emit the complete fixture state.

    Parallel nodes are serialized only for this semantic test. A second iteration
    exits before executing its body, so serialization cannot hide nontrivial
    parallelism. The existing C harness supplies Loop integer/range semantics.
    """
    body, stack = [], []
    for line in loop.splitlines():
        line = line.strip()
        if not line or line in ('context();', 'context(N);'):
            continue
        parallel = line.startswith('parallel for ')
        plain = line[len('parallel '):] if parallel else line
        if plain.startswith('for '):
            if not re.fullmatch(r'for [A-Za-z_][A-Za-z_0-9]* in range\(.+\) \{', plain):
                raise AssertionError('unsupported loop header: ' + line)
            if parallel:
                body.append('{ unsigned polcert_trip_count = 0;')
            body.extend(transpile_line(plain))
            if parallel:
                body.append('if (++polcert_trip_count > 1) return 91;')
            stack.append(parallel)
        elif line.startswith('if ') and line.endswith(' {'):
            body.extend(transpile_line(line))
            stack.append(False)
        elif line == '}':
            if not stack:
                raise AssertionError('unbalanced Loop braces')
            body.append('}')
            if stack.pop():
                body.append('}')
        elif re.fullmatch(r'A\[.+\]\[.+\] = .+;', line):
            body.extend(transpile_line(line))
        else:
            raise AssertionError('unsupported regression Loop node: ' + line)
    if stack:
        raise AssertionError('unbalanced Loop braces')
    if fixture == 'innerpar':
        rows, columns = 16, 16
        initialization = 'for (int k=0;k<16;k++) { A[k][0]=1; A[0][k]=1; }'
    elif fixture == 'vanished':
        rows, columns = 1, 10000
        initialization = 'A[0][0]=1;'
    else:
        raise AssertionError('unknown regression fixture')
    return '''#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#define min(a,b) ((a)<(b)?(a):(b))
#define max(a,b) ((a)>(b)?(a):(b))
''' + INTEGER_HELPERS_C + '''
''' + f'''#define N {columns}
static long long A[{rows}][{columns}];
''' + '''
int main(void) {
''' + initialization + '\n' + '\n'.join(body) + f'''
  for (int i=0;i<{rows};i++) for (int j=0;j<{columns};j++) printf("%lld\\n", A[i][j]);
''' + '''
  return 0;
}
'''


def checked_state(loop, work, label, compiler, run, fixture='innerpar'):
    source, executable = work / (label + '.c'), work / label
    source.write_text(render_checked_state(loop, fixture))
    built = run([compiler, '-O0', '-std=c99', '-fsanitize=undefined',
                 '-fno-sanitize-recover=all', source, '-o', executable])
    if built.returncode:
        raise AssertionError('semantic harness failed to compile:\n' + built.stdout)
    result = run([executable])
    if result.returncode:
        raise AssertionError('non-singleton parallel loop or failed semantic execution: ' + str(result.returncode))
    values = tuple(int(value) for value in result.stdout.splitlines())
    if len(values) != (256 if fixture == 'innerpar' else 10000):
        raise AssertionError('semantic harness omitted array cells')
    return values


def validate_checked_result(proc, reference, work, label, compiler, run, strict=False,
                            fixture='innerpar', require_tiling=True):
    if strict and proc.returncode != 0:
        if ('status=rejected source=pluto-hint reason=no-certifiable-dimension' not in proc.stdout
                or '== Optimized Loop ==' in proc.stdout):
            raise AssertionError('strict failure lacked rejection evidence or emitted output')
        return 'rejected'
    if proc.returncode != 0 or (require_tiling and '[tiling-validation] route=permutable-band' not in proc.stdout):
        raise AssertionError('checked tiling did not succeed:\n' + proc.stdout)
    state = checked_state(optimized_loop(proc.stdout), work, label, compiler, run, fixture)
    if state != reference:
        raise AssertionError('checked output changed the complete A state')
    return 'state-equivalent-with-no-nontrivial-parallel-loop'
