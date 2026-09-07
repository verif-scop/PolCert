#!/usr/bin/env python3
"""Keep the constant-range unroll check independent of iterator spelling."""
import re
import unittest

from run_pluto_compat_suite import CHECKS, effect_contract_count


CHECK = next(check for check in CHECKS if check.name == 'parallel-unrolljam-constant-range')


def matches(text):
    return all(re.search(pattern, text, re.DOTALL) is not None for pattern in CHECK.effect_patterns)


class EffectPatterns(unittest.TestCase):
    def test_alpha_names(self):
        for iterator in ['i0', 'i1', 'i11']:
            with self.subTest(iterator=iterator):
                self.assertTrue(matches(
                    'parallel for ' + iterator + ' in range(0, 50) {\n'
                    '  A[((2 * ' + iterator + ') + 1)] = 0;\n}\n'))

    def test_wrong_bound(self):
        self.assertFalse(matches('parallel for i0 in range(0, 51) { A[((2 * i0) + 1)] = 0; }'))

    def test_wrong_variable(self):
        self.assertFalse(matches('parallel for i0 in range(0, 50) { A[((2 * i1) + 1)] = 0; }'))

    def test_wrong_offset(self):
        self.assertFalse(matches('parallel for i0 in range(0, 50) { A[((2 * i0) + 2)] = 0; }'))

    def test_parallel_contract_preserved(self):
        self.assertEqual(CHECK.normalized, 'parallel for')
        self.assertGreater(effect_contract_count(CHECK), 0)


if __name__ == '__main__':
    unittest.main()
