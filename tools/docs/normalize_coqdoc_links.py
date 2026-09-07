#!/usr/bin/env python3
"""Repair or disable invalid local cross-references emitted by coqdoc."""

from __future__ import annotations

import argparse
import html
import json
import posixpath
import re
from collections import defaultdict
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote


HREF_RE = re.compile(r'(?P<prefix><a\b[^>]*?\s)href="(?P<href>[^"]*)"')
LOCAL_LINE_SUFFIX_RE = re.compile(r":\d+$")
EXTERNAL_PREFIXES = ("http://", "https://", "mailto:", "javascript:", "data:")
STDLIB = "https://rocq-prover.org/doc/V8.13.2/stdlib/"


def normalize_stdlib_reexports(text: str) -> str:
    # These re-exports have no declaration anchor in the published 8.13.2
    # coqdoc pages (checked 2026-09-07). Keep their module links instead of
    # claiming an exact declaration target. This requires no build-time network.
    aliases = json.loads(Path(__file__).with_name(
        "stdlib-8.13.2-reexports.json").read_text())

    def replace(match):
        href = html.unescape(match.group("href"))
        if not href.startswith(STDLIB):
            return match.group(0)
        page, separator, fragment = href[len(STDLIB):].partition("#")
        if separator and unquote(fragment) in aliases.get(page, []):
            return (match.group("prefix") + 'href="' + STDLIB + page + '"'
                    + ' title="Re-exported declaration; module documentation"')
        return match.group(0)

    return HREF_RE.sub(replace, text).replace(
        'href="http://coq.inria.fr/"', 'href="https://rocq-prover.org/"')


class PageParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.anchors: set[str] = set()
        self.hrefs: list[str] = []

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        attributes = dict(attrs)
        for key in ("id", "name"):
            value = attributes.get(key)
            if value is not None:
                self.anchors.add(value)
        href = attributes.get("href")
        if href is not None:
            self.hrefs.append(href)


@dataclass(frozen=True)
class Page:
    path: Path
    text: str
    anchors: frozenset[str]
    hrefs: tuple[str, ...]


def parse_page(path: Path) -> Page:
    text = path.read_text(encoding="utf-8")
    parser = PageParser()
    parser.feed(text)
    return Page(path, text, frozenset(parser.anchors), tuple(parser.hrefs))


def local_target(source: str, href: str) -> tuple[str, str | None] | None:
    if href.startswith(EXTERNAL_PREFIXES):
        return None
    target, separator, fragment = href.partition("#")
    if target.startswith("/"):
        return None
    normalized = posixpath.normpath(
        posixpath.join(posixpath.dirname(source), unquote(target))
    )
    if not normalized.endswith(".html"):
        return None
    return normalized, unquote(fragment) if separator and fragment else None


def unique(items: set[tuple[str, str]]) -> tuple[str, str] | None:
    if len(items) == 1:
        return next(iter(items))
    return None


def resolve_fragment(
    target: str,
    fragment: str,
    pages: dict[str, Page],
    global_exact: dict[str, set[tuple[str, str]]],
    global_suffix: dict[str, set[tuple[str, str]]],
) -> tuple[str, str] | None:
    clean = LOCAL_LINE_SUFFIX_RE.sub("", fragment)
    last_component = clean.rsplit(".", 1)[-1]
    target_anchors = pages[target].anchors

    searches = (
        {(target, anchor) for anchor in target_anchors if anchor == clean},
        {(target, anchor) for anchor in target_anchors if anchor.endswith("." + clean)},
        global_exact.get(clean, set()),
        global_suffix.get(clean, set()),
        {
            (target, anchor)
            for anchor in target_anchors
            if anchor.rsplit(".", 1)[-1] == last_component
        },
    )
    for candidates in searches:
        resolved = unique(candidates)
        if resolved is not None:
            return resolved
    return None


def rewritten_href(source: str, target: str, fragment: str) -> str:
    relative_target = posixpath.relpath(target, posixpath.dirname(source) or ".")
    encoded_fragment = quote(fragment, safe=".:_-~")
    return f"{relative_target}#{encoded_fragment}"


def normalize(root: Path) -> tuple[int, int, int]:
    pages = {
        path.relative_to(root).as_posix(): parse_page(path)
        for path in sorted(root.rglob("*.html"))
    }
    if not pages:
        raise RuntimeError(f"no HTML files found under {root}")

    global_exact: dict[str, set[tuple[str, str]]] = defaultdict(set)
    global_suffix: dict[str, set[tuple[str, str]]] = defaultdict(set)
    for page_name, page in pages.items():
        for anchor in page.anchors:
            global_exact[anchor].add((page_name, anchor))
            components = anchor.split(".")
            for index in range(1, len(components)):
                global_suffix[".".join(components[index:])].add(
                    (page_name, anchor)
                )

    replacements: dict[tuple[str, str], str | None] = {}
    valid = 0
    repaired = 0
    disabled = 0
    missing_pages: set[tuple[str, str]] = set()

    for source, page in pages.items():
        for href in page.hrefs:
            target_and_fragment = local_target(source, href)
            if target_and_fragment is None:
                continue
            target, fragment = target_and_fragment
            if target not in pages:
                missing_pages.add((source, href))
                continue
            if fragment is None or fragment in pages[target].anchors:
                valid += 1
                continue
            resolved = resolve_fragment(
                target, fragment, pages, global_exact, global_suffix
            )
            if resolved is None:
                replacements[(source, href)] = None
                disabled += 1
            else:
                resolved_target, resolved_fragment = resolved
                replacements[(source, href)] = rewritten_href(
                    source, resolved_target, resolved_fragment
                )
                repaired += 1

    if missing_pages:
        examples = ", ".join(
            f"{source}: {href}" for source, href in sorted(missing_pages)[:5]
        )
        raise RuntimeError(f"missing local HTML targets: {examples}")

    for source, page in pages.items():
        def replace(match: re.Match[str]) -> str:
            href = html.unescape(match.group("href"))
            key = (source, href)
            if key not in replacements:
                return match.group(0)
            replacement = replacements[key]
            if replacement is None:
                return match.group("prefix").rstrip()
            return (
                match.group("prefix")
                + 'href="'
                + html.escape(replacement, quote=True)
                + '"'
            )

        rewritten = normalize_stdlib_reexports(HREF_RE.sub(replace, page.text))
        if rewritten != page.text:
            page.path.write_text(rewritten, encoding="utf-8")

    remaining = find_broken_links(root)
    if remaining:
        examples = ", ".join(
            f"{source}: {href}" for source, href in remaining[:5]
        )
        raise RuntimeError(f"broken local HTML links remain: {examples}")
    return valid, repaired, disabled


def find_broken_links(root: Path) -> list[tuple[str, str]]:
    pages = {
        path.relative_to(root).as_posix(): parse_page(path)
        for path in sorted(root.rglob("*.html"))
    }
    broken: list[tuple[str, str]] = []
    for source, page in pages.items():
        for href in page.hrefs:
            target_and_fragment = local_target(source, href)
            if target_and_fragment is None:
                continue
            target, fragment = target_and_fragment
            if target not in pages:
                broken.append((source, href))
            elif fragment is not None and fragment not in pages[target].anchors:
                broken.append((source, href))
    return broken


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="coqdoc HTML output directory")
    args = parser.parse_args()
    valid, repaired, disabled = normalize(args.root.resolve())
    print(
        "coqdoc links: "
        f"{valid} valid, {repaired} repaired, {disabled} invalid links disabled"
    )


if __name__ == "__main__":
    main()
