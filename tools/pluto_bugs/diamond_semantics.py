"""Compare all array cells in the finite diamond regression fixture."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'end_to_end_c'))
from loop_to_c import INTEGER_HELPERS_C, transpile_loop_text


def check_array_states(original, optimized_loop, work, compiler, run):
    before, rest = original.split('#pragma scop')
    _, after = rest.split('#pragma endscop')
    states = '''
  for (i=0;i<NX;i++) for (j=0;j<NY+1;j++) printf("%d\\n", ex[i][j]);
  for (i=0;i<NX+1;i++) for (j=0;j<NY;j++) printf("%d\\n", ey[i][j]);
  for (i=0;i<NX;i++) for (j=0;j<NY;j++) printf("%d\\n", hz[i][j]);
'''
    original = original.replace('return 0;', states + '\nreturn 0;')
    target = ('#include <stdlib.h>\n#include <limits.h>\n#include <stdio.h>\n'
              '#define min(a,b) ((a)<(b)?(a):(b))\n'
              '#define max(a,b) ((a)>(b)?(a):(b))\n' + INTEGER_HELPERS_C
              + before + transpile_loop_text(optimized_loop)
              + after.replace('return 0;', states + '\nreturn 0;'))
    for seed in (0, 1, 7):
        outputs = []
        for label, text in [('source', original), ('target', target)]:
            text = text.replace('3 * i - j;', f'3 * i - j + {seed};')
            text = text.replace('i + 2 * j;', f'i + 2 * j - {seed};')
            text = text.replace('4 * i + j;', f'4 * i + j + {2 * seed};')
            source = work / f'{label}-{seed}.c'
            executable = work / f'{label}-{seed}'
            source.write_text(text)
            build = run([compiler, '-O0', '-std=c99', '-fsanitize=undefined,bounds',
                         '-fno-sanitize-recover=all', source, '-o', executable])
            if build.returncode:
                raise AssertionError('array-state harness build failed:\n' + build.stdout)
            result = run([executable])
            if result.returncode:
                raise AssertionError('array-state harness failed:\n' + result.stdout)
            values = tuple(int(line) for line in result.stdout.splitlines())
            if len(values) != 24:
                raise AssertionError('expected checksum and all 23 array cells')
            outputs.append(values)
        if outputs[0] != outputs[1]:
            raise AssertionError(f'diamond array-state mismatch for seed={seed}: {outputs}')
        print(f'[pluto-diamond-nointra] seed={seed} complete-array-state=match')
