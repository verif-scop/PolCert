"""Check experiment inputs and selection without running an experiment."""
import tempfile
import unittest
from pathlib import Path

from evaluation_io import read_json, sha
from run_evaluation import input_path, materialize_manifest, select_retention_plan

ROOT = Path(__file__).resolve().parents[1]


class ExperimentInputs(unittest.TestCase):
    def test_retention_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            plan_path, plan = select_retention_plan(ROOT, Path(directory))
            self.assertTrue(plan_path.is_file())
            self.assertFalse(plan['subset'])
            count = 0
            for collection in plan['collections']:
                manifest_path = plan_path.parent / collection['manifest']
                self.assertEqual(sha(manifest_path), collection['manifest_sha256'])
                manifest = read_json(manifest_path)
                count += len(manifest['cases'])
                for row in manifest['cases']:
                    self.assertTrue(Path(row['loop_input']).is_file())
            self.assertEqual(count, plan['planned_pairs'])

    def test_timing_inputs(self):
        data = materialize_manifest(ROOT, read_json(ROOT / 'manifests/timing.json'))
        self.assertTrue(data['cases'])
        for row in data['cases']:
            self.assertEqual(sha(row['loop_input']), row['source_sha256'])

    def test_subset(self):
        with tempfile.TemporaryDirectory() as directory:
            _, plan = select_retention_plan(ROOT, Path(directory),
                                             ['primary-rectangular'], ['matmul'])
            self.assertTrue(plan['subset'])
            self.assertEqual(plan['planned_pairs'], 1)

    def test_bad_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                select_retention_plan(ROOT, Path(directory), ['missing-cohort'])
            with self.assertRaises(ValueError):
                select_retention_plan(ROOT, Path(directory), kernels=['missing-kernel'])

    def test_input_boundary(self):
        for path in ('../README.md', '/etc/passwd', 'missing.loop'):
            with self.assertRaises(ValueError):
                input_path(ROOT, path)

    def test_content_addressed_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            name = '0' * 64 + '.c'
            (root / name).write_text('int main(void) { return 0; }\n')
            with self.assertRaises(ValueError):
                input_path(root, name)


if __name__ == '__main__':
    unittest.main()
