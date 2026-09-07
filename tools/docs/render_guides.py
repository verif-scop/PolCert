#!/usr/bin/env python3
"""Render repository guides and connect their source links to coqdoc pages."""

import argparse
import html
import os
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

import markdown

from normalize_coqdoc_links import parse_page


def relative(target, parent):
    return Path(os.path.relpath(target, parent)).as_posix()


def source_anchor(source, fragment, anchors):
    """Resolve a source-line link only when it names one unique declaration."""
    match = re.fullmatch(r"L(\d+)", fragment)
    if not match:
        return fragment if fragment in anchors else ""
    lines = source.read_text().splitlines()
    line = int(match[1])
    if not 1 <= line <= len(lines):
        raise ValueError(f"invalid source line: {source}#{fragment}")
    declaration = re.match(
        r"\s*(?:(?:Local|Global|Polymorphic)\s+)?"
        r"(?:Theorem|Lemma|Definition|Fixpoint|Inductive|Record|Module)\s+([\w']+)",
        lines[line - 1],
    )
    if not declaration:
        raise ValueError(f"source link does not name a declaration: {source}#{fragment}")
    name = declaration[1]
    matches = {a for a in anchors if a == name or a.endswith('.' + name)}
    if len(matches) != 1:
        raise ValueError(f"ambiguous coqdoc declaration: {source}#{fragment}: {matches}")
    return next(iter(matches))


def render(root, output):
    # Source archives and Docker mounts need not contain usable Git metadata.
    sources = set(root.glob('*.md')) | set((root / 'doc').glob('*.md'))
    for directory in ('syntax', 'samples', 'tests', 'tools'):
        sources.update((root / directory).rglob('*.md'))
    sources.add(root / 'VPL/README.md')
    guides = {p: output / 'guides' / p.relative_to(root).with_suffix('.html')
              for p in sorted(sources)}
    pages = {p.name: parse_page(p) for p in output.glob('polcert.*.html')}

    for source, destination in guides.items():
        def rewrite(match):
            url = html.unescape(match[1])
            parts = urlsplit(url)
            if parts.scheme or parts.netloc or not parts.path:
                return match[0]
            target = (source.parent / unquote(parts.path)).resolve()
            if target.is_dir() and target / 'README.md' in guides:
                target /= 'README.md'
            fragment = unquote(parts.fragment)
            if target in guides:
                target = guides[target]
            elif target.suffix == '.v' and root in target.parents:
                page_name = 'polcert.' + '.'.join(target.relative_to(root).with_suffix('').parts) + '.html'
                if page_name in pages:
                    fragment = source_anchor(target, fragment, pages[page_name].anchors)
                    target = output / page_name
            result = relative(target, destination.parent)
            if fragment:
                result += '#' + fragment
            return 'href="' + html.escape(result, quote=True) + '"'

        body = markdown.markdown(source.read_text(), extensions=['extra', 'toc'])
        body = re.sub(r'href="([^"]+)"', rewrite, body)
        destination.parent.mkdir(parents=True, exist_ok=True)
        title = next((line.lstrip('# ').strip() for line in source.read_text().splitlines() if line.startswith('# ')), source.stem)
        destination.write_text(
            '<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            '<title>' + html.escape(title) + '</title></head><body>'
            '<main class="guide">' + body + '</main></body></html>\n'
        )

    (output / 'reader.css').write_text((root / 'doc/reader.css').read_text())
    for page in output.rglob('*.html'):
        text = page.read_text()
        css = relative(output / 'reader.css', page.parent)
        nav = '<nav aria-label="Documentation">' + ' · '.join(
            '<a href="' + relative(output / target, page.parent) + '">' + label + '</a>'
            for target, label in [
                ('index.html', 'Documentation'),
                ('guides/doc/VERIFIED_PIPELINE.html', 'Pipeline'),
                ('guides/doc/PROOF_READING_GUIDE.html', 'Proof Guide'),
                ('declarations.html', 'Declarations'),
            ]
        ) + '</nav>'
        text = text.replace('</head>', '<link rel="stylesheet" href="' + css + '"></head>')
        text = re.sub(r'<body[^>]*>', lambda match: match[0] + '\n' + nav, text, count=1)
        page.write_text(text)
    print(f'Rendered {len(guides)} guides with source navigation')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    render(Path(__file__).resolve().parents[2], args.output.resolve())
