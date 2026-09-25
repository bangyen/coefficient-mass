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

Every inequality checked here also has a control: a false variant, such as
the root ``r = 5/4`` where the paper says it fails or a bound just below the
true value, that the same check must catch, so a window or a tree too small
to see anything cannot pass.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations

import pytest


def _rz(zeros: tuple[int, ...], s: int) -> Fraction:
    value = Fraction(1)
    for z in zeros:
        value *= 1 - Fraction(s, z)
    return value


def _power_sum(head, poly, deg: int, top: int, r: Fraction) -> Fraction:
    """``sum_{s=1}^{top} head(s) r^-s + sum_{s>top} poly(s) r^-s``, exactly.

    ``head`` and ``poly`` take integer values, and ``poly`` is a polynomial of
    degree at most ``deg``.  With ``x = 1/r = q/p`` the whole series is
    ``sum_{s>=0} poly(s) x^s = sum_j (Delta^j poly)(0) x^j / (1-x)^(j+1)``;
    everything is kept over the denominators ``p^top`` and ``(p-q)^(deg+1)``.
    """
    p, q = r.numerator, r.denominator
    row = [poly(s) for s in range(deg + 1)]
    diffs = []
    for _ in range(deg + 1):
        diffs.append(row[0])
        row = [b - a for a, b in zip(row, row[1:], strict=False)]
    d = p - q
    whole = Fraction(
        p * sum(c * q**j * d ** (deg - j) for j, c in enumerate(diffs)), d ** (deg + 1)
    )
    near = sum(
        ((head(s) if s else 0) - poly(s)) * q**s * p ** (top - s)
        for s in range(top + 1)
    )
    return whole + Fraction(near, p**top)


def _pz(zeros: tuple[int, ...], s: int) -> int:
    """``prod_z (z - s)``, so that ``r_Z(s)`` is this over ``prod Z``."""
    value = 1
    for z in zeros:
        value *= z - s
    return value


def _prod(zeros: tuple[int, ...]) -> int:
    return _pz(zeros, 0)


def _phi(zeros: tuple[int, ...], r: Fraction) -> Fraction:
    """``Phi_r(Z) = sum_{s>=1} |r_Z(s)| r^-s``, exactly: past ``max Z`` the
    polynomial ``r_Z`` has the sign ``(-1)^|Z|``."""
    sign = (-1) ** len(zeros)
    total = _power_sum(
        lambda s: abs(_pz(zeros, s)),
        lambda s: sign * _pz(zeros, s),
        len(zeros),
        max(zeros, default=0),
        r,
    )
    return total / _prod(zeros)


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


def _vertex_optimal(zeros: tuple[int, ...], fixed: set[int], r: Fraction) -> bool:
    """``lem:vertexopt``: whether ``Phi_r(Z) = mu_r(S, |Z|+1)``, ``S = fixed``.

    Everything is scaled by ``prod(Z - y)``: ``e_y(s)`` is ``s * _pz(rest, s)``.
    """
    top, sign = max(zeros), (-1) ** len(zeros)
    for y in set(zeros) - fixed:
        rest = tuple(z for z in zeros if z != y)

        def head(s: int, rest: tuple[int, ...] = rest) -> int:
            if s in zeros:
                return 0
            return (1 if _pz(zeros, s) > 0 else -1) * s * _pz(rest, s)

        def tail(s: int, rest: tuple[int, ...] = rest) -> int:
            return sign * s * _pz(rest, s)

        g = _power_sum(head, tail, len(zeros), top, r)
        if abs(g) > abs(y * _pz(rest, y)) * r**-y:
            return False
    return True


def _far_gap(zeros: tuple[int, ...], m: int, t: int, r: Fraction) -> Fraction:
    """``t^(m-1) Delta_{q,m}(t)`` of ``lem:farzeros`` for ``q = r_Z``, exactly.

    The weight is ``-s t^(m-1)`` for ``s <= t`` and ``(s-t) s^(m-1) - t^m``
    above; past ``max(Z, t)`` the summand is a polynomial.
    """
    sign = (-1) ** len(zeros)

    def above(s: int) -> int:
        return (s - t) * s ** (m - 1) - t**m

    def head(s: int) -> int:
        weight = -s * t ** (m - 1) if s <= t else above(s)
        return weight * abs(_pz(zeros, s))

    total = _power_sum(
        head,
        lambda s: sign * above(s) * _pz(zeros, s),
        len(zeros) + m,
        max(max(zeros, default=0), t),
        r,
    )
    return total / _prod(zeros)


def _tail_threshold(zeros: tuple[int, ...], r: Fraction) -> int:
    """The least ``sigma >= max Z`` with ``2 R_p(sigma) <= Psi_r(p)``, ``p = r_Z``.

    ``2 R_p(sigma) - Psi_r(p)`` is ``Delta_{p,1}(sigma)``.
    """
    sigma = max(zeros)
    while _far_gap(zeros, 1, sigma, r) > 0:
        sigma += 1
    return sigma


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
    certifies ``eta_sigma(n) <= bound`` at.

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
    """``prop:secondrowexact`` (a), (b): ``V(16,2) = 1/Phi(Z_2) = 1/nu_3(14)``,
    below ``beta(15) = min_{i<=3} 1/nu_i(15)``."""
    top = _phi(_VERTEX, BELOW)
    assert _vertex_optimal(_VERTEX, {2}, BELOW)
    assert _vertex_optimal(_Y1, set(), BELOW)
    assert _phi(_Y1, BELOW) < top
    assert _tail_threshold(_Y1, BELOW) == 107
    assert _second_row_bounded(BELOW, _Y1, _Y2, top, {2: _VERTEX}) == []
    assert Fraction(65694, 10**4) < 1 / top < Fraction(65695, 10**4)
    assert Fraction(76492, 10**4) < 1 / _phi(_Y1, BELOW) < Fraction(76493, 10**4)
    # (b): nu_2(15), nu_3(15) <= nu_1(15) < Phi(Z_2), so k = 3 fails too.
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
    ``V(19,2) = 1/Phi(Z_3) = 1/nu_4(16) < beta(18)``, and ``eta_2(18) < nu_1(18)``."""
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


# Every row (``sec:finiterows``).  For a polynomial ``q_N`` through the
# exempted positions ``N`` found so far, ``lem:farzeros`` gives a threshold
# from which the ``m - |N|`` positions still to come cost nothing; the
# positions below the thresholds form a finite tree (``thm:finiterows``).


def _far_threshold(zeros: tuple[int, ...], m: int, r: Fraction) -> int:
    """The least ``t >= 1`` with ``Delta_{q,m}(t) <= 0``, ``q = r_Z``.

    Bisection, as ``Delta_{q,m}`` does not increase (``lem:farzeros`` (a));
    the certificates below need only ``Delta_{q,m}(t) <= 0``, checked here.
    """
    lo, hi = 0, 1
    while _far_gap(zeros, m, hi, r) > 0:
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if _far_gap(zeros, m, mid, r) > 0:
            lo = mid
        else:
            hi = mid
    assert _far_gap(zeros, m, hi, r) <= 0
    return hi


def _through(base: tuple[int, ...], exempt: tuple[int, ...]) -> list[tuple[int, ...]]:
    """``base`` with each position of ``exempt`` that it misses put in place
    of one of the two elements outside ``exempt`` nearest to it."""
    out = [set(base)]
    for sigma in exempt:
        grown = []
        for zs in out:
            if sigma in zs:
                grown.append(zs)
                continue
            near = sorted(
                (z for z in zs if z not in exempt), key=lambda z: (abs(z - sigma), z)
            )
            grown.extend(zs - {z} | {sigma} for z in near[:2])
        out = grown
    return [tuple(sorted(zs)) for zs in out]


def _row_cover(
    r: Fraction,
    n: int,
    m: int,
    bound: Fraction,
    root: tuple[int, ...],
    fulls: dict[int, list[tuple[int, ...]]],
    exceptions: dict[tuple[int, ...], tuple[int, ...]],
    strict: bool = False,
) -> list[tuple[int, ...]]:
    """The nodes of the tree of ``thm:finiterows`` (b) for
    ``V_r(n+m, m+1) >= 1/bound`` that no zero set certifies.

    A node ``N`` (``|N| < m``) needs a zero set ``Z_N`` through ``N`` with at
    most ``n+|N|-1`` zeros and ``Phi_r(Z_N) <= bound``; its children are
    ``N + {sigma}`` for ``max N < sigma < T_N``, ``T_N`` the far threshold of
    ``Z_N`` for the ``m-|N|`` positions still to come.  A leaf ``S``
    (``|S| = m``) needs a zero set through ``S`` with at most ``n+m-1`` zeros
    and ``Phi_r <= bound``.  Each is the cheapest of a few sets built from its
    parent's set and from ``fulls`` (keyed by size), or ``exceptions[S]``.
    With ``strict``, every set but the exceptions must have ``Phi_r < bound``.
    """
    uncovered: list[tuple[int, ...]] = []

    def fits(value: Fraction, exempt: tuple[int, ...]) -> bool:
        return value < bound or (
            value == bound and (not strict or exempt in exceptions)
        )

    def visit(exempt: tuple[int, ...], zeros: tuple[int, ...]) -> None:
        assert set(exempt) <= set(zeros) and len(zeros) <= n + len(exempt) - 1
        if not fits(_phi(zeros, r), exempt):
            uncovered.append(exempt)
            return
        if len(exempt) == m:
            return
        top = _far_threshold(zeros, m - len(exempt), r)
        for sigma in range(max(exempt, default=0) + 1, top):
            child = (*exempt, sigma)
            if child in exceptions:
                visit(child, exceptions[child])
                continue
            if sigma in zeros:
                cands = [zeros]
            else:
                near = sorted(
                    (z for z in zeros if z not in exempt), key=lambda z: abs(z - sigma)
                )
                cands = [tuple(sorted(set(zeros) - {z} | {sigma})) for z in near[:3]]
                cands.append(tuple(sorted({*zeros, sigma})))
            for base in fulls.get(n + len(child) - 1, []):
                cands += _through(base, child)
            cands = [c for c in cands if len(c) <= n + len(child) - 1]
            visit(child, min(cands, key=lambda c: _phi(c, r)))

    visit((), root)
    return uncovered


def test_far_zeros() -> None:
    """``lem:farzeros`` at the ``nu_1(15)``-optimum, ``r = 5/4``: the
    thresholds for one, two and three far zeros, and zeros past them."""
    base = _phi(_Y1, BELOW)
    thresholds = [_far_threshold(_Y1, m, BELOW) for m in (1, 2, 3)]
    assert thresholds == [25, 51, 66]
    # For m = 1 the threshold is thm:secondrow's sigma_*.
    assert _far_gap(_Y1, 1, 24, BELOW) > 0
    for m, t in zip((1, 2, 3), thresholds, strict=True):
        for far in combinations((t, t + 1, t + 2, t + 7, 2 * t), m):
            assert _phi(tuple(sorted({*_Y1, *far})), BELOW) <= base, far
    # The control: two zeros at the one-zero threshold cost half as much again.
    assert _phi(tuple(sorted({*_Y1, 25, 26})), BELOW) > Fraction(3, 2) * base


# ``prop:thirdrowexact`` (a): at ``r = 4/3``, ``n = 12`` the worst pair of
# exempted positions is ``{2, 3}``, below the second row.
_R43 = Fraction(4, 3)
#: ``nu_1(12)``, ``eta_2(12) = nu_3(11)`` and ``mu({2,3}, 14)``.
_Y12 = (1, 3, 6, 9, 13, 17, 23, 30, 39, 50, 64)
_ETA12 = (1, 2, 5, 8, 12, 16, 21, 28, 35, 44, 56, 71)
_PAIR12 = (2, 3, 4, 7, 10, 15, 19, 25, 32, 40, 49, 61, 77)
_FULL12 = {
    12: [(1, 3, 5, 8, 12, 16, 21, 28, 35, 44, 56, 71)],
    13: [(1, 3, 5, 8, 11, 15, 20, 26, 32, 40, 50, 62, 77)],
}


def test_third_row_below_second() -> None:
    """``V_{4/3}(14,3) = 1/Phi(Z_23) < V_{4/3}(13,2) = 1/nu_3(11) <
    beta(12) = min_{i<=3} 1/nu_i(12)``, and ``{2,3}`` alone attains it."""
    assert _far_threshold(_Y12, 2, _R43) == 33
    r, pair, eta, top = _R43, _phi(_PAIR12, _R43), _phi(_ETA12, _R43), _phi(_Y12, _R43)
    # eta_2(12) = nu_3(11), as [1, 2] lies in its optimum, while Z_23 omits 1.
    assert {1, 2} <= set(_ETA12) and 1 not in _PAIR12
    assert _vertex_optimal(_PAIR12, {2, 3}, r)
    assert _vertex_optimal(_ETA12, {2}, r)
    assert _vertex_optimal(_Y12, set(), r)
    assert top < eta < pair
    # nu_2(12), nu_3(12) and nu_4(12) are below nu_1(12), so by lem:rowmono
    # the prefix identity fails at (4/3, 15, 4) as well.
    assert _phi(_FULL12[12][0], r) < top
    assert _phi((1, 2, 5, 7, 11, 15, 20, 25, 32, 40, 50, 61, 77), r) < top
    assert _phi((1, 2, 3, 7, 10, 14, 18, 23, 29, 37, 45, 55, 67, 83), r) < top
    # The second row: every position is certified at eta_2(12).
    assert _row_cover(r, 12, 1, eta, _Y12, _FULL12, {(2,): _ETA12}) == []
    # The third row: every pair, strictly below mu({2,3}) except {2,3}.
    assert (
        _row_cover(r, 12, 2, pair, _Y12, _FULL12, {(2, 3): _PAIR12}, strict=True) == []
    )
    assert Fraction(77168, 10**4) < 1 / pair < Fraction(77169, 10**4)
    assert Fraction(85482, 10**4) < 1 / eta < Fraction(85483, 10**4)
    assert Fraction(88501, 10**4) < 1 / top < Fraction(88502, 10**4)
    # The control: at the second row's value the pair {2,3}, and only it, fails.
    assert _row_cover(r, 12, 2, eta, _Y12, _FULL12, {}) == [(2, 3)]


# ``prop:thirdrowexact`` (b): at ``r = 4/3``, ``n = 14`` the prefix identity
# holds in the second row and fails in the third.
_Y14 = (1, 3, 5, 8, 11, 15, 20, 26, 32, 40, 50, 62, 77)
_PAIR14 = (1, 2, 3, 6, 9, 13, 17, 22, 27, 34, 41, 50, 60, 73, 89)
_FULL14 = {
    14: [(1, 3, 5, 7, 10, 14, 18, 24, 30, 37, 45, 55, 67, 83)],
    15: [(1, 3, 4, 7, 10, 13, 17, 22, 28, 34, 42, 50, 61, 73, 90)],
}


def test_third_row_fails_alone() -> None:
    """``V_{4/3}(15,2) = beta(14) = min_{i<=3} 1/nu_i(14) > V_{4/3}(16,3) =
    1/Phi(Z_23) = 1/nu_4(13)``, attained at the pair ``{2,3}`` alone."""
    assert _far_threshold(_Y14, 2, _R43) == 36
    r, pair, top = _R43, _phi(_PAIR14, _R43), _phi(_Y14, _R43)
    # mu({2,3}, 16) = nu_4(13), as [1, 3] lies in its optimum.
    assert {1, 2, 3} <= set(_PAIR14)
    assert _vertex_optimal(_PAIR14, {2, 3}, r)
    assert _vertex_optimal(_Y14, set(), r)
    assert top < pair
    # nu_2(14), nu_3(14) and nu_4(14) are below nu_1(14), so by lem:rowmono
    # the prefix identity fails at (4/3, 17, 4) as well.
    assert _phi(_FULL14[14][0], r) < top
    assert _phi((1, 2, 4, 7, 10, 13, 17, 22, 28, 34, 42, 50, 61, 73, 90), r) < top
    assert _phi((1, 2, 3, 6, 9, 12, 16, 21, 26, 32, 39, 46, 55, 66, 79, 96), r) < top
    # The second row is the top row: every position is certified at nu_1(14).
    assert _row_cover(r, 14, 1, top, _Y14, _FULL14, {}) == []
    # The third row: every pair, strictly below mu({2,3}, 16) except {2,3}.
    assert (
        _row_cover(r, 14, 2, pair, _Y14, _FULL14, {(2, 3): _PAIR14}, strict=True) == []
    )
    assert Fraction(146268, 10**4) < 1 / pair < Fraction(146269, 10**4)
    assert Fraction(150390, 10**4) < 1 / top < Fraction(150391, 10**4)
    # The control: at nu_1(14) the second row passes but the pair {2,3} fails.
    assert _row_cover(r, 14, 2, top, _Y14, _FULL14, {}) == [(2, 3)]


# ``prop:thirdrowexact`` (c): at ``r = 3/2``, ``n = 8`` the third row is the top
# row, with ``nu_2(8), nu_3(8) < nu_1(8)``.
_R32 = Fraction(3, 2)
_Y8 = (1, 3, 6, 9, 14, 20, 28)
_FULL8 = {8: [(1, 3, 5, 8, 12, 17, 24, 33)], 9: [(1, 3, 5, 8, 11, 15, 21, 28, 37)]}
#: The closest pair: ``mu({2,3}, 10)``, one percent below ``nu_1(8)``.
_PAIR8 = (2, 3, 4, 7, 10, 15, 20, 27, 37)


def test_third_row_is_top_row() -> None:
    """``V_{3/2}(10,3) = beta(8) = min_{i<=3} 1/nu_i(8)``, minimum at ``i = 1``."""
    r, top = _R32, _phi(_Y8, _R32)
    assert _vertex_optimal(_Y8, set(), r)
    assert _phi(_FULL8[8][0], r) < top
    assert _phi((1, 2, 5, 7, 11, 15, 21, 28, 37), r) < top
    assert _vertex_optimal(_PAIR8, {2, 3}, r)
    assert _phi(_PAIR8, r) < top
    assert _row_cover(r, 8, 2, top, _Y8, _FULL8, {(2, 3): _PAIR8}) == []
    assert Fraction(80259, 10**4) < 1 / top < Fraction(80260, 10**4)
    # The control: a bound a millionth below nu_1(8) is not certified.
    below = top * (1 - Fraction(1, 10**6))
    assert _row_cover(r, 8, 2, below, _Y8, _FULL8, {(2, 3): _PAIR8}) == [()]
