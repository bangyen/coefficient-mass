"""Exact checks of ``coefficient-mass-rows.tex`` and its roadmap entry.

The paper reduces every row to the dual problem
``mu_r(S, L) = min Phi_r(q)`` over ``q`` of degree below ``L`` with
``q(0) = 1`` and ``q|_S = 0``, where ``Phi_r(q) = sum_{s>=1} |q(s)| r^-s``,
and minimizers can be taken as ``r_Z(s) = prod_{z in Z} (1 - s/z)`` for
integer zero sets ``Z`` (``lem:intzeros``).  So on a window of integers every
quantity here is a finite minimum of exact rationals.

``Phi_r(Z)`` is exact, not truncated: past ``max Z`` the polynomial ``r_Z``
keeps the sign ``(-1)^|Z|``, and ``sum_{s>=0} q(s) x^s`` is
``sum_j (Delta^j q)(0) x^j / (1-x)^(j+1)``.

Every inequality checked here also has a control at ``r = 5/4``, where the
paper says it fails, so a window too small to see anything cannot pass.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb

import pytest


def _rz(zeros: tuple[int, ...], s: int) -> Fraction:
    value = Fraction(1)
    for z in zeros:
        value *= 1 - Fraction(s, z)
    return value


def _phi(zeros: tuple[int, ...], r: Fraction) -> Fraction:
    """``Phi_r(Z) = sum_{s>=1} |r_Z(s)| r^-s``, exactly."""
    x = 1 / r
    values = [_rz(zeros, s) for s in range(len(zeros) + 1)]
    # sum_{s>=0} r_Z(s) x^s through the forward differences of r_Z at 0.
    whole = sum(
        sum((-1) ** (j - i) * comb(j, i) * values[i] for i in range(j + 1))
        * x**j
        / (1 - x) ** (j + 1)
        for j in range(len(zeros) + 1)
    )
    top = max(zeros, default=0)
    head = [_rz(zeros, s) * x**s for s in range(1, top + 1)]
    tail = whole - 1 - sum(head)
    return sum(abs(h) for h in head) + (-1) ** len(zeros) * tail


def test_phi_is_exact() -> None:
    """The closed form agrees with a long partial sum and ``Phi_r(0) = a``."""
    r = Fraction(3)
    assert _phi((), r) == 1 / (r - 1)
    zeros = (1, 3, 4)
    partial = sum(abs(_rz(zeros, s)) * r**-s for s in range(1, 200))
    assert 0 <= _phi(zeros, r) - partial < Fraction(1, 10**60)


def _mu(fixed: tuple[int, ...], size: int, r: Fraction, window: int) -> Fraction:
    """``min Phi_r(Z)`` over ``Z`` of ``size`` in ``[1, window]``, ``Z >= fixed``."""
    rest = [s for s in range(1, window + 1) if s not in fixed]
    return min(
        _phi(tuple(sorted(fixed + extra)), r)
        for extra in combinations(rest, size - len(fixed))
    )


#: Roots at and above 2 for the theorems, and the control root below 2.
ROOTS = [Fraction(2), Fraction(5, 2), Fraction(3)]
BELOW = Fraction(5, 4)


@pytest.mark.parametrize("r", ROOTS)
@pytest.mark.parametrize("big_l", [2, 3, 4])
def test_last_row_at_least_two(r: Fraction, big_l: int) -> None:
    """``cor:lastrowr``, ``r >= 2``: ``Phi_r(S) <= a`` for ``|S| = L-1``."""
    a = 1 / (r - 1)
    for zeros in combinations(range(1, 11), big_l - 1):
        assert _phi(zeros, r) <= a, zeros


@pytest.mark.parametrize("r", [Fraction(5, 4), Fraction(3, 2), Fraction(2)])
@pytest.mark.parametrize("big_l", [2, 3, 4])
def test_last_row_below_two(r: Fraction, big_l: int) -> None:
    """``cor:lastrowr``, ``r <= 2``: the maximum of ``Phi_r(S)`` is ``a^L``.

    It is attained at ``S = [1, L-1]``; below 2 that exceeds ``a``, which is
    the control on the ``r >= 2`` case.
    """
    a = 1 / (r - 1)
    prefix = tuple(range(1, big_l))
    assert _phi(prefix, r) == a**big_l
    for zeros in combinations(range(1, 11), big_l - 1):
        assert _phi(zeros, r) <= a**big_l, zeros
    assert r == 2 or _phi(prefix, r) > a


def _rows_are_top_rows(r: Fraction, big_l: int, k: int) -> list[tuple[int, ...]]:
    """The exempted sets ``S`` at which ``mu(S, L) > mu(0, n)`` on a window.

    ``thm:allrowstwo`` says ``V_r(L,k) = beta_r(n)``, ``n = L-k+1``, that is,
    ``mu_r(S, L) <= mu_r(0, n)`` for every ``|S| = k-1``.
    """
    window = 14
    top = _mu((), big_l - k, r, window)
    return [
        exempt
        for exempt in combinations(range(1, 9), k - 1)
        if _mu(exempt, big_l - 1, r, window) > top
    ]


@pytest.mark.parametrize("r", ROOTS)
@pytest.mark.parametrize(("big_l", "k"), [(2, 2), (3, 2), (3, 3), (4, 2), (4, 3)])
def test_every_row_is_a_top_row(r: Fraction, big_l: int, k: int) -> None:
    """``thm:allrowstwo``: at ``r >= 2`` no exempted set beats the top row."""
    assert _rows_are_top_rows(r, big_l, k) == []


def test_rows_are_not_top_rows_below_two() -> None:
    """The control: at ``r = 5/4`` the same search finds the sets that beat it."""
    assert (1,) in _rows_are_top_rows(BELOW, 2, 2)
    assert _rows_are_top_rows(BELOW, 3, 2)


# The roadmap's counterexample to the prefix identity at ``r = 5/4``,
# ``L = 16``, ``k = 2``, ``n = 15``, as exact certificates.  The zero sets are
# the optima of a local search; the checks below need only that they are
# feasible, not that they are optimal.

#: ``Phi(Z)`` over ``Z`` containing the exempted distance ``2``: the vertex
#: that the primal multiple is read off from.
_EXEMPT = 2
_VERTEX = (1, 2, 5, 8, 12, 17, 22, 28, 35, 44, 53, 65, 78, 94, 115)
#: ``nu_1(15) <= Phi(Y_1)`` and ``nu_2(15) = mu([1], 16) <= Phi({1} + Y_2)``.
_Y1 = (1, 3, 6, 9, 13, 18, 24, 30, 38, 47, 58, 71, 87, 107)
_Y2 = (1, 3, 5, 8, 12, 17, 22, 28, 36, 44, 54, 65, 78, 94, 115)


def _solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    n = len(matrix)
    a = [[*row, b] for row, b in zip(matrix, rhs, strict=True)]
    for col in range(n):
        piv = next(i for i in range(col, n) if a[i][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        for i in range(n):
            if i != col and a[i][col] != 0:
                f = a[i][col] / a[col][col]
                a[i] = [u - f * v for u, v in zip(a[i], a[col], strict=True)]
    return [a[i][n] / a[i][i] for i in range(n)]


def _prefix_counterexample(degree: int) -> list[Fraction]:
    """A monic multiple of ``(x - 5/4)^16``, top coefficient first.

    Complementary slackness at the vertex: every coefficient off the vertex
    has magnitude ``t`` and the sign of ``-r_Z``; the 15 on it and ``t`` are
    fixed by the 16 divisibility conditions ``sum_s g_s s^j r^-s = 0``.
    """
    r, big_l = BELOW, 16
    signs = {
        s: (-1 if _rz(_VERTEX, s) > 0 else 1)
        for s in range(1, degree + 1)
        if s not in _VERTEX
    }
    matrix = [
        [sum(sign * s**j * r**-s for s, sign in signs.items())]
        + [Fraction(z) ** j * r**-z for z in _VERTEX]
        for j in range(big_l)
    ]
    t, *on_vertex = _solve(matrix, [Fraction(-1 if j == 0 else 0) for j in range(16)])
    g = {0: Fraction(1), **{s: sign * t for s, sign in signs.items()}}
    g.update(zip(_VERTEX, on_vertex, strict=True))
    return [g[s] for s in range(degree + 1)]


def test_prefix_identity_fails_below_two() -> None:
    """``V_{5/4}(16, 2) <= 6.5695 < 7.6492 <= min_{i<=2} 1/nu_i(15)``."""
    coeffs = _prefix_counterexample(300)
    # The multiple really is one: 16 exact synthetic divisions by x - 5/4.
    poly = coeffs
    for _ in range(16):
        quotient = [poly[0]]
        for c in poly[1:]:
            quotient.append(c + BELOW * quotient[-1])
        assert quotient.pop() == 0
        poly = quotient
    b = sorted((abs(c) for c in coeffs[1:]), reverse=True)
    assert b[0] == abs(coeffs[_EXEMPT])
    assert b[1] <= Fraction(65695, 10**4)
    assert 1 / _phi(_Y1, BELOW) >= Fraction(76492, 10**4)
    assert 1 / _phi(_Y2, BELOW) >= Fraction(76492, 10**4)


# The second row (``sec:secondrow``).  ``lem:vertexopt`` certifies a vertex
# exactly, ``thm:secondrow`` (a) disposes of every exempted position from a
# tail threshold on, and each position below it gets an explicit zero set.


def _series_tail(f, deg: int, x: Fraction, start: int) -> Fraction:
    """``sum_{s>start} f(s) x^s`` for a polynomial ``f`` of degree ``<= deg``."""
    values = [Fraction(f(s)) for s in range(deg + 1)]
    whole = sum(
        sum((-1) ** (j - i) * comb(j, i) * values[i] for i in range(j + 1))
        * x**j
        / (1 - x) ** (j + 1)
        for j in range(deg + 1)
    )
    return whole - sum(f(s) * x**s for s in range(start + 1))


def _vertex_optimal(zeros: tuple[int, ...], fixed: set[int], r: Fraction) -> bool:
    """``lem:vertexopt``: whether ``Phi_r(Z) = mu_r(S, |Z|+1)``, ``S = fixed``."""
    x, top, sign = 1 / r, max(zeros), (-1) ** len(zeros)
    signs = {
        s: (1 if _rz(zeros, s) > 0 else -1) for s in range(1, top + 1) if s not in zeros
    }
    for y in set(zeros) - fixed:
        rest = tuple(z for z in zeros if z != y)

        def e(s: int, rest: tuple[int, ...] = rest) -> Fraction:
            return s * _rz(rest, s)

        g = sum(sg * e(s) * x**s for s, sg in signs.items())
        g += sign * _series_tail(e, len(zeros), x, top)
        if abs(g) > abs(e(y)) * x**y:
            return False
    return True


def _tail_threshold(zeros: tuple[int, ...], r: Fraction) -> int:
    """The least ``sigma >= max Z`` with ``2 T_p(sigma) <= M(p)``, ``p = r_Z``."""
    x, top, sign = 1 / r, max(zeros), (-1) ** len(zeros)
    deg = len(zeros) + 1
    moment = sum(s * abs(_rz(zeros, s)) * x**s for s in range(1, top + 1))
    moment += sign * _series_tail(lambda s: s * _rz(zeros, s), deg, x, top)
    sigma = top
    while True:

        def f(s: int, sigma: int = sigma) -> Fraction:
            return (s - sigma) * _rz(zeros, s)

        tail = _series_tail(f, deg, x, sigma)
        if 2 * sign * tail <= moment:
            return sigma
        sigma += 1


def _candidates(sigma: int, full: tuple[int, ...], short: tuple[int, ...]):
    """Zero sets of size ``|full|`` through ``sigma``: ``full`` itself, the
    insertion ``ins(short, sigma)``, and ``full`` with one zero moved."""
    if sigma in full:
        yield full
    if sigma not in short:
        yield tuple(
            [z for z in short if z < sigma]
            + [sigma]
            + [z + 1 for z in short if z > sigma]
        )
    for z in sorted(full, key=lambda z: abs(z - sigma)):
        if sigma not in full:
            yield tuple(sorted(set(full) - {z} | {sigma}))


def _second_row_bounded(
    r: Fraction,
    short: tuple[int, ...],
    full: tuple[int, ...],
    bound: Fraction,
    exceptions: dict[int, tuple[int, ...]],
) -> list[int]:
    """The positions below the tail threshold of ``short`` that no zero set
    certifies ``mu_sigma(n) <= bound`` at.

    ``short`` has ``n-1`` zeros; when ``Phi_r(short) <= bound``,
    ``thm:secondrow`` (a) with ``p = r_short`` covers every ``sigma`` from its
    tail threshold on.  Below it each ``sigma`` needs a zero set of size ``n``
    through ``sigma`` with ``Phi_r <= bound``.
    """
    uncovered = []
    for sigma in range(1, _tail_threshold(short, r)):
        if sigma in exceptions:
            zs = exceptions[sigma]
            assert sigma in zs and len(zs) == len(full) and _phi(zs, r) <= bound
            continue
        if not any(_phi(zs, r) <= bound for zs in _candidates(sigma, full, short)):
            uncovered.append(sigma)
    return uncovered


def test_vertex_certificate() -> None:
    """``lem:vertexopt`` accepts the optima and rejects a displaced zero."""
    assert _vertex_optimal(_VERTEX, {2}, BELOW)
    assert _vertex_optimal(_VERTEX, {1, 2}, BELOW)
    assert _vertex_optimal(_Y1, set(), BELOW)
    assert _vertex_optimal(_Y2, {1}, BELOW)
    # The controls: a displaced zero, and the constrained optimum offered as
    # an unconstrained one.
    assert not _vertex_optimal((*_VERTEX[:-2], 95, 115), {2}, BELOW)
    assert not _vertex_optimal(_VERTEX, set(), BELOW)


def test_tail_threshold() -> None:
    """``thm:secondrow`` (a): past the threshold, ``Phi_r((1-s/sigma) p)`` is
    at most ``Phi_r(p)``, for ``p`` the ``nu_1(15)``-optimum."""
    threshold = _tail_threshold(_Y1, BELOW)
    for sigma in (threshold, threshold + 5, 3 * threshold):
        assert _phi(tuple(sorted({*_Y1, sigma})), BELOW) <= _phi(_Y1, BELOW)
    # The control: at sigma = 2 the extra zero costs, it does not save.
    assert _phi((*_Y1[:1], 2, *_Y1[1:]), BELOW) > _phi(_Y1, BELOW)


def test_second_row_at_five_fourths_fails() -> None:
    """``prop:secondrowexact`` (a), (b): ``V(16,2) = 1/Phi(Z*) = 1/nu_3(14)``,
    below ``beta(15) = min_{i<=3} 1/nu_i(15)``."""
    top = _phi(_VERTEX, BELOW)
    assert _vertex_optimal(_VERTEX, {2}, BELOW)
    assert _vertex_optimal(_Y1, set(), BELOW)
    assert _phi(_Y1, BELOW) < top
    assert _tail_threshold(_Y1, BELOW) == 107
    assert _second_row_bounded(BELOW, _Y1, _Y2, top, {2: _VERTEX}) == []
    assert Fraction(65694, 10**4) < 1 / top < Fraction(65695, 10**4)
    assert Fraction(76492, 10**4) < 1 / _phi(_Y1, BELOW) < Fraction(76493, 10**4)
    # (b): nu_2(15), nu_3(15) <= nu_1(15) < Phi(Z*), so k = 3 fails too.
    nu3 = (1, 2, 5, 8, 11, 16, 21, 26, 33, 41, 50, 60, 71, 85, 102, 123)
    assert _phi(_Y2, BELOW) < _phi(_Y1, BELOW)
    assert _phi(nu3, BELOW) < _phi(_Y1, BELOW)
    # The control: the prefix bound nu_1(15) of eq:prefixid fails at sigma = 2.
    assert _second_row_bounded(BELOW, _Y1, _Y2, _phi(_Y1, BELOW), {}) == [2]


def test_second_row_at_five_fourths_holds() -> None:
    """``prop:secondrowexact`` (c): ``V(14,2) = beta(13) > 1`` with
    ``nu_2(13) < nu_1(13)``, the prefix identity with its minimum at ``i = 1``."""
    short = (1, 3, 6, 10, 15, 21, 27, 36, 45, 57, 72, 91)
    full = (1, 3, 6, 9, 14, 19, 25, 33, 41, 52, 64, 79, 99)
    nu1 = _phi(short, BELOW)
    assert _vertex_optimal(short, set(), BELOW)
    assert _tail_threshold(short, BELOW) == 91
    assert _second_row_bounded(BELOW, short, full, nu1, {}) == []
    assert _phi(full, BELOW) < nu1 < 1
    assert Fraction(46297, 10**4) < 1 / nu1 < Fraction(46298, 10**4)
    # The control: the bound nu_2(13) of a minimum at i = k fails at sigma = 2.
    assert 2 in _second_row_bounded(BELOW, short, full, _phi(full, BELOW), {})


def test_second_row_at_four_thirds() -> None:
    """``prop:secondrowexact`` (d): at ``r = 4/3`` a worst position is ``3``:
    ``V(19,2) = 1/Phi(Z) = 1/nu_4(16) < beta(18)``, and ``mu_2(18) < nu_1(18)``."""
    r = Fraction(4, 3)
    short = (1, 2, 4, 6, 9, 12, 16, 20, 25, 30, 36, 44, 52, 61, 72, 85, 103)
    full = (1, 2, 4, 6, 8, 11, 15, 19, 23, 28, 34, 41, 48, 57, 66, 78, 91, 109)
    worst = (1, 2, 3, 6, 8, 11, 15, 18, 23, 28, 34, 41, 48, 57, 66, 78, 91, 109)
    top = _phi(worst, r)
    assert _vertex_optimal(worst, {3}, r)
    assert _vertex_optimal(short, set(), r)
    assert _phi(full, r) < _phi(short, r) < top
    assert _tail_threshold(short, r) == 103
    assert _second_row_bounded(r, short, full, top, {3: worst}) == []
    assert Fraction(4138, 100) < 1 / top < Fraction(4139, 100)
    assert Fraction(4234, 100) < 1 / _phi(short, r) < Fraction(4235, 100)
    # The control: the prefix bound nu_1(18) fails at sigma = 3 and only there.
    assert _second_row_bounded(r, short, full, _phi(short, r), {}) == [3]
