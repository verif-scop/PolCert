#!/usr/bin/env python3
"""Check negative-producer phase injection without running a compiler."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


frozen = load('frozen_nonpermutable', ROOT / 'tools/tiling_routes/frozen_nonpermutable_pluto.py')
rejecting = load('rejecting', Path(__file__).with_name('rejecting_pluto.py'))
FIXTURES = ROOT / 'tools/tiling_routes/fixtures'


class PhaseWrapperProtocol(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.source = Path(self.directory.name) / 'input.scop'
        self.source.write_text('test input\n')
        self.mid = self.output('midtransform')
        self.post = self.output('posttile')
        self.final = self.output('afterscheduling')
        self.mid.write_bytes((FIXTURES / 'nonpermutable-band.midtransform.scop').read_bytes())
        self.post.write_bytes((FIXTURES / 'nonpermutable-band.posttile.scop').read_bytes())
        self.final.write_bytes(self.post.read_bytes())

    def output(self, phase):
        return self.source.with_name(self.source.name + '.' + phase + '.scop')

    def invoke(self, module, flags, mode='tiling'):
        stderr = io.StringIO()
        with patch.object(module.sys, 'argv', ['wrapper', '--dumpscop', '--readscop', *flags, str(self.source)]), \
                patch.object(module.subprocess, 'run', return_value=SimpleNamespace(returncode=0)), \
                patch.dict(os.environ, {'POLCERT_REJECTING_PLUTO_MODE': mode}), \
                contextlib.redirect_stderr(stderr):
            result = module.main()
        return result, stderr.getvalue()

    def test_frozen_single_invocation_binds_all_three_files(self):
        self.mid.write_text('original midpoint')
        self.post.write_text('original tiled')
        self.final.write_text('original final')
        result, stderr = self.invoke(frozen, ['--tile'])
        self.assertEqual(result, 0)
        self.assertEqual(self.mid.read_bytes(), (FIXTURES / 'nonpermutable-band.midtransform.scop').read_bytes())
        self.assertEqual(self.post.read_bytes(), (FIXTURES / 'nonpermutable-band.posttile.scop').read_bytes())
        self.assertEqual(self.post.read_bytes(), self.final.read_bytes())
        self.assertEqual(stderr.count('phase=affine '), 1)
        self.assertEqual(stderr.count('phase=tiled '), 1)

    def test_frozen_staged_affine_still_exports_midpoint(self):
        result, stderr = self.invoke(frozen, ['--notile'])
        self.assertEqual(result, 0)
        self.assertEqual(self.final.read_bytes(), self.mid.read_bytes())
        self.assertEqual(stderr.count('phase=affine '), 1)
        self.assertNotIn('phase=tiled ', stderr)

    def test_frozen_missing_phase_is_not_silently_created(self):
        self.post.unlink()
        result, _ = self.invoke(frozen, ['--tile'])
        self.assertEqual(result, 71)
        self.assertFalse(self.post.exists())

    def test_plain_tile_link_corrupts_both_aliases_once(self):
        original = self.post.read_bytes()
        midpoint = self.mid.read_bytes()
        result, stderr = self.invoke(rejecting, ['--tile'])
        self.assertEqual(result, 0)
        self.assertNotEqual(self.post.read_bytes(), original)
        self.assertEqual(self.post.read_bytes(), self.final.read_bytes())
        self.assertEqual(self.mid.read_bytes(), midpoint)
        self.assertEqual(stderr.count('corrupted one tiling tile-link'), 1)

    def test_plain_scattering_corrupts_both_aliases(self):
        original = self.post.read_bytes()
        result, stderr = self.invoke(rejecting, ['--tile'], 'tiling-schedule')
        self.assertEqual(result, 0)
        self.assertNotEqual(self.post.read_bytes(), original)
        self.assertEqual(self.post.read_bytes(), self.final.read_bytes())
        self.assertEqual(stderr.count('[rejecting-pluto] reversed '), 1)

    def test_plain_existing_phase_difference_is_not_hidden(self):
        original = self.post.read_bytes()
        self.final.write_text('a different final proposal')
        with self.assertRaisesRegex(ValueError, 'already differ'):
            self.invoke(rejecting, ['--tile'])
        self.assertEqual(self.post.read_bytes(), original)
        self.assertEqual(self.final.read_text(), 'a different final proposal')

    def test_diamond_tiling_keeps_final_separate(self):
        original = self.final.read_bytes()
        result, _ = self.invoke(rejecting, ['--tile', '--diamond-tile'])
        self.assertEqual(result, 0)
        self.assertNotEqual(self.post.read_bytes(), original)
        self.assertEqual(self.final.read_bytes(), original)

    def test_diamond_final_affine_keeps_tiling_separate(self):
        original = self.post.read_bytes()
        result, stderr = self.invoke(rejecting, ['--tile', '--diamond-tile'], 'final-affine')
        self.assertEqual(result, 0)
        self.assertEqual(self.post.read_bytes(), original)
        self.assertNotEqual(self.final.read_bytes(), original)
        self.assertEqual(stderr.count('[rejecting-pluto] reversed '), 1)


if __name__ == '__main__':
    unittest.main()
