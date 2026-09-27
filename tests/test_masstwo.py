"""Each check of :mod:`tests.masstwo` as a test of its own.

``just masstwo`` prints the tables; this names the check that fails.
"""

from __future__ import annotations

import pytest

from tests import masstwo


@pytest.mark.parametrize("label", list(masstwo.CHECKS))
def test_exact_check(label: str) -> None:
    failures: list[str] = []
    assert masstwo.CHECKS[label](failures) > 0
    assert not failures, failures


def test_rows_clear_the_published_constant() -> None:
    """The summed rows beat ``prop:quadratic``'s ``L**2/80`` at every ``L``."""
    for L in masstwo._ROW_L:
        prod, _ = masstwo._row_sum(L)
        assert masstwo._log(prod) > L**2 / 80


def test_sixteenth_holds_from_ninetyseven() -> None:
    """``L**2/16`` from ``L = 97``, and not before: the threshold is sharp."""
    prod, _ = masstwo._row_sum(97)
    assert masstwo._log(prod) >= 97**2 / 16
    prod, _ = masstwo._row_sum(96)
    assert masstwo._log(prod) < 96**2 / 16
