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


def test_rows_clear_the_elementary_constant() -> None:
    """The summed rows beat ``prop:quadratic`` at every sampled ``L``."""
    for L in masstwo._ROW_L:
        prod, _ = masstwo._row_sum(L)
        assert masstwo._log(prod) > L**2 / 80


def test_sixteenth_at_ninetyseven_not_ninetysix() -> None:
    """Check ``L**2/16`` at ``L = 97`` and its failure at ``L = 96``."""
    prod, _ = masstwo._row_sum(97)
    assert masstwo._log(prod) >= 97**2 / 16
    prod, _ = masstwo._row_sum(96)
    assert masstwo._log(prod) < 96**2 / 16
