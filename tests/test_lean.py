"""The Lean library cites the papers' results by the numbers they carry.

``CoefficientMass/`` names each statement it formalizes in a docstring --
``Theorem 3.2 (coefficient order statistics)`` -- and :mod:`numbering`
explains why a number has to be checked against the source.  This holds
every such reference to the label it means, and each headline theorem (a
``theorem name : Statement``) to the result it proves, so renumbering a
paper or renaming a theorem cannot leave the formalization describing the
wrong statement.
"""

from __future__ import annotations

import re

import pytest

from tools.numbering import PAPERS, ROOT, numbering

LEAN = sorted(
    [ROOT / "CoefficientMass.lean", *(ROOT / "CoefficientMass").rglob("*.lean")]
)

#: The paper a comment cites when it names none.
DEFAULT = "coefficient-mass"

#: Every numbered reference in a Lean comment, as ``(paper, number) ->
#: (word, label)``.  The test also checks the reverse: that every such
#: reference in the library is listed.
REFERENCES = {
    ("coefficient-mass", "2.1"): ("Lemma", "lem:consecutive"),
    ("coefficient-mass", "2.2"): ("Theorem", "thm:tail"),
    ("coefficient-mass", "2.3"): ("Lemma", "lem:interlace"),
    ("coefficient-mass", "3.1"): ("Lemma", "lem:slack"),
    ("coefficient-mass", "3.2"): ("Theorem", "thm:order"),
    ("coefficient-mass", "3.3"): ("Corollary", "cor:complex"),
    ("coefficient-mass", "3.4"): ("Corollary", "cor:mass"),
    ("coefficient-mass", "4.4"): ("Proposition", "prop:sharp23"),
    ("coefficient-mass", "4.5"): ("Lemma", "lem:rowcert"),
    ("coefficient-mass", "4.6"): ("Lemma", "lem:confdel"),
    ("coefficient-mass", "4.7"): ("Lemma", "lem:holeint"),
    ("coefficient-mass", "4.8"): ("Lemma", "lem:twohole"),
    ("coefficient-mass", "4.9"): ("Proposition", "prop:rowsfree"),
    ("coefficient-mass", "4.13"): ("Theorem", "thm:everyrow"),
}

#: Each headline theorem, ``theorem name : Statement``, as ``name ->
#: (Statement, paper, label)``: the ``Prop`` it proves and the result that
#: ``Prop`` states.  ``zeroBound`` is the classical input, not a result of
#: the papers.
HEADLINES = {
    "zeroBound": ("ZeroBound", None, None),
    "consecutiveTail": ("ConsecutiveTail", "coefficient-mass", "lem:consecutive"),
    "tailBound": ("TailBound", "coefficient-mass", "thm:tail"),
    "tailEquality": ("TailEquality", "coefficient-mass", "thm:tail"),
    "orderStatistics": ("OrderStatistics", "coefficient-mass", "thm:order"),
    "logarithmicMass": ("LogarithmicMass", "coefficient-mass", "cor:mass"),
    "firstRowCertificate": ("FirstRowCertificate", "coefficient-mass", "lem:slack"),
    "firstRowOrderStatistics": (
        "FirstRowOrderStatistics",
        "coefficient-mass",
        "thm:order",
    ),
    "rowCertificate": ("RowCertificate", "coefficient-mass", "lem:rowcert"),
    "deleteLargest": ("DeleteLargest", "coefficient-mass", "lem:confdel"),
    "holeIntegral": ("HoleIntegral", "coefficient-mass", "lem:holeint"),
    "rowsFree": ("RowsFree", "coefficient-mass", "prop:rowsfree"),
    "sharpRowTwo": ("SharpRowTwo", "coefficient-mass", "prop:sharp23"),
}

_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_REFERENCE = re.compile(r"(Theorem|Lemma|Corollary|Proposition) (\d+\.\d+)")
_PAPER = re.compile(r"`(coefficient-mass[a-z-]*)\.tex`")
_HEADLINE = re.compile(r"^theorem (\w+) : ([A-Z]\w*) :=", re.MULTILINE)


def _cited() -> set[tuple[str, str, str]]:
    """The ``(word, paper, number)`` references the library's comments make.

    A comment's paper is the first ``.tex`` it names, else ``DEFAULT``.
    """
    found: set[tuple[str, str, str]] = set()
    for path in LEAN:
        for comment in _COMMENT.findall(path.read_text()):
            named = _PAPER.search(comment)
            paper = named.group(1) if named else DEFAULT
            for match in _REFERENCE.finditer(comment):
                found.add((match.group(1), paper, match.group(2)))
    return found


def _headlines() -> dict[str, str]:
    """Each headline theorem's name, mapped to the statement it proves."""
    return {
        name: statement
        for path in LEAN
        for name, statement in _HEADLINE.findall(path.read_text())
    }


def _labels(paper: str) -> set[str]:
    return set(re.findall(r"\\label\{([^}]*)\}", (PAPERS / f"{paper}.tex").read_text()))


def test_patterns_match() -> None:
    """The patterns still match: a blind test would pass on anything."""
    assert len(_cited()) >= len(REFERENCES)
    assert len(_headlines()) >= len(HEADLINES)


@pytest.mark.parametrize(("reference", "expected"), sorted(REFERENCES.items()))
def test_reference_resolves(
    reference: tuple[str, str], expected: tuple[str, str]
) -> None:
    """Each cited number is the labelled result of the paper it names."""
    paper, number = reference
    numbered = numbering(paper)
    assert number in numbered, f"{paper} has no result {number}"
    word, label, _ = numbered[number]
    assert (word, label) == expected


def test_every_reference_is_covered() -> None:
    """No comment cites a result by a number this table does not list."""
    listed = {
        (word, paper, number) for (paper, number), (word, _) in REFERENCES.items()
    }
    assert _cited() == listed


@pytest.mark.parametrize(("name", "expected"), sorted(HEADLINES.items()))
def test_headline_proves(
    name: str, expected: tuple[str, str | None, str | None]
) -> None:
    """Each headline theorem proves the statement of the result it names."""
    statement, paper, label = expected
    assert _headlines().get(name) == statement, f"no `theorem {name} : {statement}`"
    if paper is not None:
        assert label in _labels(paper), f"{paper} has no {label}"


def test_every_headline_is_covered() -> None:
    """No headline theorem goes unlisted."""
    assert set(_headlines()) == set(HEADLINES)
