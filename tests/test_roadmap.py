"""Every result the roadmap cites exists in the paper it links.

``ROADMAP.md`` names results by label -- ``thm:transfer``, ``sec:scope`` --
and each entry links the papers it draws on.  A label renamed or removed in a
paper leaves the roadmap pointing at nothing, silently; this holds each
backticked label to a ``\\label`` in one of the papers its entry links.
"""

from __future__ import annotations

import re

import pytest

from tools.numbering import PAPERS

ROADMAP = PAPERS / "ROADMAP.md"

_LINK = re.compile(r"\]\(([^)]+\.tex)\)")
_CITED = re.compile(r"`((?:thm|lem|cor|prop|sec|eq):[A-Za-z0-9]+)`")
_DEFINED = re.compile(r"\\label\{([^}]*)\}")


def _entries() -> list[str]:
    """The roadmap's bullets, one string each."""
    return re.split(r"\n(?=- )", ROADMAP.read_text())[1:]


def _cases() -> list[tuple[str, str, tuple[str, ...]]]:
    cases = []
    for entry in _entries():
        papers = tuple(dict.fromkeys(_LINK.findall(entry)))
        title = re.search(r"\*\*(.+?)\*\*", entry)
        name = title.group(1) if title else entry[:40]
        for label in dict.fromkeys(_CITED.findall(entry)):
            cases.append((name, label, papers))
    return cases


def test_roadmap_cites_labels() -> None:
    """The label pattern still matches: a blind test would pass on anything."""
    assert len(_cases()) >= 40


@pytest.mark.parametrize(("entry", "label", "papers"), _cases())
def test_label_exists(entry: str, label: str, papers: tuple[str, ...]) -> None:
    assert papers, f"{entry!r} links no paper"
    defined = {
        found
        for paper in papers
        for found in _DEFINED.findall((PAPERS / paper).read_text())
    }
    assert label in defined, f"{entry!r} cites {label}, not in {papers}"
