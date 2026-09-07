import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from innerpar_semantics import checked_state, optimized_loop, render_checked_state, validate_checked_result
from innerpar_unsafe_hint import unsafe_hint


def run(command):
    return subprocess.run([str(x) for x in command], stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, timeout=10)


class InnerparSemanticsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)
        self.cc = shutil.which('cc')
        if not self.cc:
            self.skipTest('C compiler unavailable')
        self.reference = checked_state('context();', self.work, 'reference', self.cc, run)

    def accepted(self, loop):
        return SimpleNamespace(returncode=0, stdout='== Optimized Loop ==\n' + loop +
                               '\n[tiling-validation] route=permutable-band\n')

    def validate(self, loop, strict=False):
        return validate_checked_result(self.accepted(loop), self.reference,
                                       self.work, 'candidate', self.cc, run, strict=strict)

    def test_sequential_and_singleton_strict_and_nonstrict(self):
        for strict in (False, True):
            for loop in ('context();', 'parallel for renamed in range(7, 8) {\n}',
                         'for outer in range(0, 4) {\nparallel for p in range(outer, outer+1) {\n}\n}'):
                self.assertIn('state-equivalent', self.validate(loop, strict))

    def test_nontrivial_parallel_at_later_outer_environment_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'non-singleton'):
            self.validate('for outer in range(0, 3) {\nparallel for p in range(0, outer) {\n}\n}')

    def test_nontrivial_second_parallel_node_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'non-singleton'):
            self.validate('parallel for x in range(0, 1) {\n}\nparallel for y in range(3, 5) {\n}')

    def test_changed_nonfinal_cell_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'complete A state'):
            self.validate('A[2][3] = 19;')

    def test_vanished_fixture_and_guarded_singleton(self):
        source = 'context(N);\nfor i in range(0, 1) {\nfor j in range(1, N) {\nA[i][j] = A[i][j-1] + 1;\n}\n}'
        reference = checked_state(source, self.work, 'vanished-reference', self.cc, run, fixture='vanished')
        output = self.accepted('if (2 <= N) {\n' + source.replace('for i', 'parallel for i').replace('context(N);\n', '') + '\n}')
        self.assertIn('state-equivalent', validate_checked_result(output, reference, self.work, 'vanished', self.cc, run, strict=True, fixture='vanished'))
        self.assertEqual(reference, tuple(range(1, 10001)))

    def test_strict_rejection_requires_alarm_and_no_output(self):
        rejection = SimpleNamespace(returncode=2, stdout='status=rejected source=pluto-hint reason=no-certifiable-dimension')
        self.assertEqual(validate_checked_result(rejection, (), self.work, 'unused', self.cc, run, strict=True), 'rejected')
        for output in ('unrelated failure', rejection.stdout+'\n== Optimized Loop ==\n'):
            with self.assertRaises(AssertionError):
                validate_checked_result(SimpleNamespace(returncode=2, stdout=output), (), self.work, 'unused', self.cc, run, strict=True)

    def test_unsupported_or_unbalanced_syntax_fails_closed(self):
        for text in ('mystery();', '}', 'for x in range(0, 1) {', 'vector for x in range(0, 1) {\n}'):
            with self.assertRaises(AssertionError):
                render_checked_state(text)
        with self.assertRaises(AssertionError):
            optimized_loop('no marker')


class UnsafeHintWitnessTests(unittest.TestCase):
    def fixture(self):
        def rel(name, outputs, inputs, rows):
            return name + '\n' + ' '.join(map(str, [len(rows), outputs+inputs+2, outputs, inputs, 0, 0])) + '\n' + '\n'.join(' '.join(map(str, row)) for row in rows) + '\n'
        # Instance variables tile_i,tile_j,i,j. Both chosen instances satisfy
        # these nonnegative-domain constraints and floor-division tile bounds.
        domain = [[1, 0, 0, 1, 0, -1], [1, 0, 0, 0, 1, -1],
                  [1, -2, 0, 1, 0, 0], [1, 2, 0, -1, 0, 1],
                  [1, 0, -2, 0, 1, 0], [1, 0, 2, 0, -1, 1]]
        maps = [[0,0,0,0], [1,0,0,0], [0,0,0,0], [0,1,0,0],
                [0,0,1,0], [0,0,0,0], [0,0,0,1], [0,0,0,0]]
        scattering = [[0] + [-int(i==j) for j in range(8)] + row + [0] for i,row in enumerate(maps)]
        access = [[0,-1,0,0,0,0,0,0,1], [0,0,-1,0,0,0,1,0,0], [0,0,0,-1,0,0,0,1,0]]
        read = [row[:] for row in access]
        read[-1][-1] = -1
        return '<OpenScop>\n' + rel('DOMAIN',4,0,domain) + rel('SCATTERING',8,4,scattering) + rel('WRITE',3,4,access) + rel('READ',3,4,read) + '<scatnames>\na b c dependent e f g h\n</scatnames>\n</OpenScop>\n'

    def test_witness_selects_semantic_coordinate_not_iterator_spelling(self):
        original = self.fixture()
        changed, witness = unsafe_hint(original)
        self.assertEqual(witness['hinted_iterator'], 'dependent')
        self.assertEqual(witness['source_write'], [1,2,1])
        self.assertEqual(witness['schedules'][0][:3], witness['schedules'][1][:3])
        import re
        self.assertEqual(re.sub(r'<loop>.*?</loop>\n', '', changed, flags=re.S), original)

    def test_missing_dependence_or_invalid_domain_fails(self):
        original = self.fixture()
        with self.assertRaises(AssertionError):
            unsafe_hint(original.replace('0 0 0 -1 0 0 0 1 -1', '0 0 0 -1 0 0 0 1 7'))
        with self.assertRaises(AssertionError):
            unsafe_hint(original.replace('1 0 0 1 0 -1', '1 0 0 1 0 -9'))


if __name__ == '__main__':
    unittest.main()
