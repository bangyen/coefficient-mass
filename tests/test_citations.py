"""The papers' numbered cross-references resolve to the results they name.

The three companions cite ``coefficient-mass.tex`` by number --
``\\cite[Theorem~2.2]{coefficient-mass}``.  :mod:`numbering` explains why a
number has to be checked against the source; this holds every such citation
to the paper and the label it is supposed to name.  The expectations are
labels, not numbers, because the label is what the citing sentence means.

``bangyen/esolangs`` cites these papers too, from a pinned tag; its own
``tests/proofs/test_citations.py`` keeps the numbers it relies on.
"""

from __future__ import annotations

import re

import pytest

from tools.numbering import PAPERS, numbering

#: Every numbered cross-reference between the papers, as
#: ``(citing file, cited paper, number) -> (word, label)``.  The test also
#: checks the reverse: that every such reference in a citing file is listed.
CITATIONS = {
    ("coefficient-mass-attainment.tex", "coefficient-mass", "2.1"): (
        "Lemma",
        "lem:consecutive",
    ),
    ("coefficient-mass-attainment.tex", "coefficient-mass", "2.2"): (
        "Theorem",
        "thm:tail",
    ),
    ("coefficient-mass-attainment.tex", "coefficient-mass", "3.1"): (
        "Lemma",
        "lem:slack",
    ),
    ("coefficient-mass-attainment.tex", "coefficient-mass", "3.2"): (
        "Theorem",
        "thm:order",
    ),
    ("coefficient-mass-attainment.tex", "coefficient-mass", "4.4"): (
        "Proposition",
        "prop:sharp23",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "2.1"): (
        "Lemma",
        "lem:consecutive",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "3.2"): (
        "Theorem",
        "thm:order",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "3.3"): (
        "Corollary",
        "cor:complex",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "3.4"): (
        "Corollary",
        "cor:mass",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "3.7"): (
        "Corollary",
        "cor:near",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "4.2"): (
        "Proposition",
        "prop:quadratic",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "4.3"): (
        "Corollary",
        "cor:allroots",
    ),
    ("coefficient-mass-complex.tex", "coefficient-mass", "4.4"): (
        "Proposition",
        "prop:sharp23",
    ),
    ("coefficient-mass-rows.tex", "coefficient-mass", "2.1"): (
        "Lemma",
        "lem:consecutive",
    ),
    ("coefficient-mass-rows.tex", "coefficient-mass", "2.2"): ("Theorem", "thm:tail"),
    ("coefficient-mass-rows.tex", "coefficient-mass", "2.3"): (
        "Lemma",
        "lem:interlace",
    ),
    ("coefficient-mass-rows.tex", "coefficient-mass", "3.2"): ("Theorem", "thm:order"),
    ("coefficient-mass-rows.tex", "coefficient-mass", "4.5"): ("Lemma", "lem:rowcert"),
    ("coefficient-mass-rows.tex", "coefficient-mass", "4.6"): ("Lemma", "lem:confdel"),
    ("coefficient-mass-rows.tex", "coefficient-mass", "4.13"): (
        "Theorem",
        "thm:everyrow",
    ),
}

#: The files whose citations the table above has to cover.
CITING = (
    "coefficient-mass-attainment.tex",
    "coefficient-mass-complex.tex",
    "coefficient-mass-rows.tex",
)

#: A numbered reference in running text or in a ``\cite`` option.
_REFERENCE = re.compile(r"(Theorem|Lemma|Corollary|Proposition)[~ ]+(\d+\.\d+)")

#: The paper a line cites: the key of its ``\cite``.
_CITE_KEY = re.compile(r"\\cite\[[^]]*\]\{([^}]*)\}")


def _cited(name: str) -> set[tuple[str, str, str]]:
    """The ``(word, paper, number)`` references to a companion ``name`` makes.

    The paper is the key the line's own ``\\cite`` names.  A numbered
    reference on a line that names none is the file's reference to itself;
    one whose key is not a paper here is somebody else's, which is what skips
    the two ``Theorem~4.1`` citations of Karlin and Studden.
    """
    found: set[tuple[str, str, str]] = set()
    for line in (PAPERS / name).read_text().splitlines():
        cite = _CITE_KEY.search(line)
        if cite is None or not (PAPERS / f"{cite.group(1)}.tex").exists():
            continue
        for match in _REFERENCE.finditer(line):
            found.add((match.group(1), cite.group(1), match.group(2)))
    return found


@pytest.mark.parametrize(("citation", "expected"), sorted(CITATIONS.items()))
def test_citation_resolves(
    citation: tuple[str, str, str], expected: tuple[str, str]
) -> None:
    """Each cited number is the labelled result of the paper it names."""
    _, paper, number = citation
    numbered = numbering(paper)
    assert number in numbered, f"{paper} has no result {number}"
    word, label, _ = numbered[number]
    assert (word, label) == expected


def test_every_citation_is_covered() -> None:
    """No file cites a companion by a number this table does not list."""
    for name in CITING:
        listed = {
            (word, paper, number)
            for (file, paper, number), (word, _) in CITATIONS.items()
            if file == name
        }
        assert _cited(name) == listed, name
