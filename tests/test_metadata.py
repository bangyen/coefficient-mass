"""The citation metadata and the package metadata agree.

``CITATION.cff`` is what a citing repository reads, ``pyproject.toml`` what
the release workflow checks the tag against; a version bumped in one and not
the other would tag one version and cite another.
"""

from __future__ import annotations

import re
import tomllib

from tools.numbering import ROOT


def _cff(key: str) -> str:
    found = re.search(rf"^{key}: (.+)$", (ROOT / "CITATION.cff").read_text(), re.M)
    assert found is not None, f"CITATION.cff has no {key}"
    return found.group(1).strip().strip('"')


def test_versions_agree() -> None:
    with open(ROOT / "pyproject.toml", "rb") as handle:
        project = tomllib.load(handle)["project"]
    assert _cff("version") == project["version"]


def test_release_date_is_a_date() -> None:
    assert re.fullmatch(r"\d{4}-\d{2}-\d{2}", _cff("date-released"))
