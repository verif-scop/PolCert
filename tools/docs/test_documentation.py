"""Focused checks for guide rendering and coqdoc navigation."""

from pathlib import Path
import tempfile
import unittest

from normalize_coqdoc_links import local_target, normalize_stdlib_reexports
from render_guides import render, source_anchor


class DocumentationTests(unittest.TestCase):
    def test_empty_fragment_is_a_page_link(self):
        self.assertEqual(local_target('index.html', 'module.html#'),
                         ('module.html', None))

    def test_stdlib_reexport_keeps_module_link(self):
        link = ('<a href="https://rocq-prover.org/doc/V8.13.2/stdlib/'
                'Coq.ZArith.BinInt.html#Z.add">Z.add</a>')
        result = normalize_stdlib_reexports(link)
        self.assertNotIn('#Z.add', result)
        self.assertIn('module documentation', result)
        self.assertIn('>Z.add</a>', result)

    def test_other_stdlib_links_are_unchanged(self):
        link = ('<a href="https://rocq-prover.org/doc/V8.13.2/stdlib/'
                'Coq.Init.Logic.html#eq">eq</a>')
        self.assertEqual(normalize_stdlib_reexports(link), link)

    def test_source_line_resolves_to_unique_declaration(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Example.v'
            source.write_text('Theorem correct : True.\nProof. exact I. Qed.\n')
            self.assertEqual(source_anchor(source, 'L1', {'Example.correct'}),
                             'Example.correct')
            for fragment, anchors in [('L2', {'Example.correct'}),
                                      ('L1', {'A.correct', 'B.correct'})]:
                with self.assertRaises(ValueError):
                    source_anchor(source, fragment, anchors)

    def test_source_archive_without_git(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'doc').mkdir()
            (root / 'VPL').mkdir()
            (root / 'README.md').write_text('# Overview\n[Guide](doc/GUIDE.md)\n')
            (root / 'doc/GUIDE.md').write_text('# Guide\n[Overview](../README.md)\n')
            (root / 'doc/reader.css').write_text('body { color: black; }\n')
            (root / 'VPL/README.md').write_text('# VPL\n')
            output = root / 'doc/proof-html'
            render(root, output)
            self.assertIn('href="doc/GUIDE.html"',
                          (output / 'guides/README.html').read_text())
            self.assertIn('href="../README.html"',
                          (output / 'guides/doc/GUIDE.html').read_text())


if __name__ == '__main__':
    unittest.main()
