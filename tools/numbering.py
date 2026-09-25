"""LaTeX's result numbering, recomputed from a paper's source.

A number is not a link: reordering or inserting a result renumbers everything
after it, and splitting a paper renumbers from the start, leaving a citation
pointing at the wrong statement -- or at no statement -- silently and while
still compiling.  So the tests recompute each paper's numbering the way LaTeX
does -- one counter shared by the four theorem environments, reset per
``\\section`` -- and hold each citation to the label it is supposed to name.

Run as a script, it prints the numbering of every result another repository
cites, for pinning there:

    python tools/numbering.py coefficient-mass:3.4 coefficient-mass-complex:2.1
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

#: The repository root, and the directory the papers live in.
ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"

#: The environments sharing one counter, from the ``\newtheorem`` block at the
#: head of each paper, mapped to the word a citation spells.
ENVIRONMENTS = {
    "theorem": "Theorem",
    "lemma": "Lemma",
    "corollary": "Corollary",
    "proposition": "Proposition",
}

#: ``\begin{corollary}[Title]`` and the ``\label`` that follows it, which may
#: sit on the next line (``prop:subtwo`` does).
_BEGIN = re.compile(r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}(?:\[([^]]*)\])?")
_LABEL = re.compile(r"\\label\{([^}]*)\}")
_SECTION = re.compile(r"^\\section\{")


def numbering(paper: str) -> dict[str, tuple[str, str, str]]:
    """Map each result number of ``paper`` to the result it names.

    The value is ``(word, label, title)``.
    """
    lines = (PAPERS / f"{paper}.tex").read_text().splitlines()
    numbered: dict[str, tuple[str, str, str]] = {}
    section = 0
    counter = 0
    for index, line in enumerate(lines):
        if _SECTION.match(line):
            section += 1
            counter = 0
            continue
        begin = _BEGIN.search(line)
        if begin is None:
            continue
        counter += 1
        # The label is on the ``\begin`` line or the one after it; nothing in
        # the papers puts anything else between the two.
        label = _LABEL.search(line) or _LABEL.search(lines[index + 1])
        assert label is not None, f"unlabelled result at line {index + 1}"
        numbered[f"{section}.{counter}"] = (
            ENVIRONMENTS[begin.group(1)],
            label.group(1),
            begin.group(2) or "",
        )
    return numbered


def main(argv: list[str]) -> int:
    """Print ``(paper, number): (word, label, title),`` for each argument."""
    for arg in argv:
        paper, number = arg.split(":")
        print(f"    ({paper!r}, {number!r}): {numbering(paper)[number]!r},")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
