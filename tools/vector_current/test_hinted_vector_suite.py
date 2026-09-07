#!/usr/bin/env python3
import unittest
import subprocess
import tempfile
from pathlib import Path

from run_hinted_vector_suite import inspect_loop, numerical_harness


POSITIVE = '''for tile in range(0, 4) {
  for row in range((32 * tile), min(100, ((32 * tile) + 32))) {
    vector for lane in range(0, 4) {
      A[((4 * row) + lane)] = ((2 * A[((4 * row) + lane)]) + 2);
    }
  }
}
'''


class HintedVectorObserverTests(unittest.TestCase):
    def test_origin_name_independent_innermost_location(self):
        shape = inspect_loop(POSITIVE)
        self.assertEqual(shape['max_loop_depth'], 3)
        self.assertEqual(shape['vectors'][0]['var'], 'lane')
        self.assertEqual(shape['vectors'][0]['depth'], 3)
        self.assertEqual(shape['assignment_vectors'], [['lane']])
        self.assertIn('record(4 * row + lane, lane);',
                      numerical_harness(POSITIVE, shape, False))

    def test_complete_numerical_harness(self):
        with tempfile.TemporaryDirectory(prefix='polcert-vector-observer-') as directory:
            root = Path(directory)
            code, binary = root / 'check.c', root / 'check'
            code.write_text(numerical_harness(POSITIVE, inspect_loop(POSITIVE), False))
            build = subprocess.run(['cc', '-O0', '-std=c99', str(code), '-o', str(binary)],
                                   capture_output=True, text=True, timeout=30)
            self.assertEqual(build.returncode, 0, build.stderr)
            check = subprocess.run([str(binary)], capture_output=True, text=True, timeout=10)
            self.assertEqual(check.returncode, 0, check.stderr)
            self.assertIn('complete_instances=400', check.stdout)

    def test_non_innermost_annotation_rejected(self):
        wrong = POSITIVE.replace('for row', 'vector for row').replace('vector for lane', 'for lane')
        with self.assertRaisesRegex(ValueError, 'encloses another loop'):
            inspect_loop(wrong)

    def test_absent_vector_effect_rejected(self):
        sequential = POSITIVE.replace('vector for lane', 'for lane')
        with self.assertRaisesRegex(ValueError, 'one innermost vector'):
            numerical_harness(sequential, inspect_loop(sequential), False)

    def test_unannotated_assignment_rejected(self):
        partly_vector = POSITIVE + 'A[0] = 0;\n'
        with self.assertRaisesRegex(ValueError, 'one innermost vector'):
            numerical_harness(partly_vector, inspect_loop(partly_vector), False)

    def test_unbalanced_output_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unclosed final loop'):
            inspect_loop(POSITIVE.rsplit('}', 1)[0])


if __name__ == '__main__':
    unittest.main()
