"""Each check of :mod:`tests.sweep` as a test of its own.

``just sweep`` prints the tallies; this names the check that fails.
"""

from __future__ import annotations

import pytest

from tests import sweep


@pytest.mark.parametrize("label", list(sweep.CHECKS))
def test_exact_check(label: str) -> None:
    failures: list[str] = []
    assert sweep.CHECKS[label](failures) > 0
    assert not failures, failures


def test_seeded_draws() -> None:
    """The stated bound fails only above the cutoff; the repaired never."""
    failures: list[str] = []
    sweep._check_draws(failures)
    assert not failures, failures
