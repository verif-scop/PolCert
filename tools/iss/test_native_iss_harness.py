"""Check that the native ISS regression cannot accept an unsplit fallback."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from run_native_iss_suite import ROOT, harness


class NativeIssHarnessTests(unittest.TestCase):
    def run_harness(self, source, optimized, rank=1, cut_axis=0):
        code, _ = harness(source, optimized, rank, cut_axis)
        with tempfile.TemporaryDirectory(prefix='iss-harness-test-') as temporary:
            directory = Path(temporary)
            (directory / 'test.c').write_text(code)
            compiled = subprocess.run(['cc', '-std=c99', str(directory / 'test.c'), '-o', str(directory / 'test')], capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            return subprocess.run([str(directory / 'test')], capture_output=True, text=True).returncode

    def test_unsplit_fallback_rejected(self):
        source = (ROOT / 'tests/end-to-end-c/cases/reverse_iss/reverse_iss.loop').read_text()
        with self.assertRaisesRegex(ValueError, 'expected split assignment sites'):
            harness(source, source)

    def test_actual_split_and_duplicate_execution(self):
        source = (ROOT / 'tests/end-to-end-c/cases/reverse_iss/reverse_iss.loop').read_text()
        split = '''context(N);
for i in range(0, ((N + 1) // 2)) {
  A[i] = (2 * A[(N - 1 - i)]);
}
for i in range(((N + 1) // 2), N) {
  A[i] = (2 * A[(N - 1 - i)]);
}
'''
        self.assertEqual(self.run_harness(source, split), 0)
        duplicate = split.replace('range(((N + 1) // 2), N)', 'range(0, N)')
        self.assertEqual(self.run_harness(source, duplicate), 12)

    def test_nonpartition_assignment_sites_rejected(self):
        source = (ROOT / 'tests/end-to-end-c/cases/reverse_iss/reverse_iss.loop').read_text()
        wrong_cut = '''context(N);
for i in range(0, 1) {
  A[i] = (2 * A[(N - 1 - i)]);
}
for i in range(1, N) {
  A[i] = (2 * A[(N - 1 - i)]);
}
'''
        self.assertEqual(self.run_harness(source, wrong_cut), 13)

    def test_two_dimensional_partitions(self):
        for name, axis in [('reverse_rows', 0), ('reverse_columns', 1)]:
            source = (ROOT / ('tests/iss-native/' + name + '.loop')).read_text()
            extent = 'N' if axis == 0 else 'M'
            left = source.replace('range(0, ' + extent + ')', 'range(0, ((' + extent + ' + 1) // 2))')
            right = source.replace('range(0, ' + extent + ')', 'range(((' + extent + ' + 1) // 2), ' + extent + ')')
            with self.subTest(kernel=name):
                self.assertEqual(self.run_harness(source, left + right, 2, axis), 0)


if __name__ == '__main__':
    unittest.main()
