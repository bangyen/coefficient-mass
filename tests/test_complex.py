"""Exact checks of ``coefficient-mass-complex.tex``.

Each bound is checked on seeded random integer multiples, where every
coefficient is exact; roots of irrational modulus are avoided by using
Pythagorean Gaussian integers.  Every group has a control that a false
variant of its statement is caught.
"""

from __future__ import annotations

import random
from collections.abc import Callable
from fractions import Fraction
from itertools import product
from math import comb, log, prod

import pytest

from tests.sweep import min_bk_of

SEED = 20260925

Poly = list[int]  # coefficients, constant term first


def _mul(p: Poly, q: Poly) -> Poly:
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def _product(factors: list[Poly]) -> Poly:
    out = [1]
    for f in factors:
        out = _mul(out, f)
    return out


def _divides(d: Poly, p: Poly) -> bool:
    """Exact division over the rationals."""
    rem = [Fraction(c) for c in p]
    while len(rem) >= len(d) and any(rem):
        if rem[-1] == 0:
            rem.pop()
            continue
        shift = len(rem) - len(d)
        f = rem[-1] / d[-1]
        for i, c in enumerate(d):
            rem[shift + i] -= f * c
        rem.pop()
    return not any(rem)


def _b(p: Poly) -> list[int]:
    """Nonleading magnitudes, largest first: ``b_1, b_2, ...``."""
    return sorted((abs(c) for c in p[:-1]), reverse=True)


def _mass(p: Poly) -> int:
    """``exp Lambda(p) = prod max(1, |f_j|)`` over all coefficients."""
    return prod(max(1, abs(c)) for c in p)


def _cofactor(rng: random.Random) -> Poly:
    degree = rng.randint(0, 4)
    q = [rng.randint(-3, 3) for _ in range(degree)] + [rng.choice([-1, 1])]
    return q


# Multisection (lem:multisection, thm:transfer).


def _sections(f: Poly, m: int) -> list[Poly]:
    return [f[e::m] for e in range(m)]


def test_multisection_transfer() -> None:
    rng = random.Random(SEED)
    for _ in range(200):
        m = rng.randint(2, 3)
        roots = [rng.choice([-3, -2, 2, 3, 5]) for _ in range(rng.randint(1, 3))]
        big_r = _product([[-z, 1] for z in roots])
        big_p = [0] * (m * (len(big_r) - 1) + 1)
        big_p[::m] = big_r
        f = _mul(big_p, _cofactor(rng))
        top = len(f) - 1
        for e, section in enumerate(_sections(f, m)):
            assert _divides(big_r, section)
            if e == top % m:
                assert section[-1] == f[-1]
                assert all(x >= y for x, y in zip(_b(f), _b(section), strict=False)), (
                    f,
                    m,
                )
                assert _mass(f) >= _mass(section)


def test_multisection_control() -> None:
    """A non-multiple fails the divisibility the lemma asserts."""
    big_r = [-2, 1]  # y - 2
    f = [-2, 1, 1]  # x^2 + x - 2: divisible by x - 1, not by x^2 - 2
    assert not all(_divides(big_r, s) for s in _sections(f, 2))


# Purely imaginary pairs (cor:imag, item 1).


def test_imaginary_pairs_rows() -> None:
    """``b_k(F) >= |f_D| prod_{j>=k} (c_j^2 - 1)`` for ``c_j^2 >= 2``."""
    rng = random.Random(SEED + 1)
    for _ in range(200):
        squares = sorted(rng.randint(2, 7) for _ in range(rng.randint(1, 4)))
        f = _mul(_product([[c2, 0, 1] for c2 in squares]), _cofactor(rng))
        b = _b(f)
        for k in range(1, len(squares) + 1):
            assert b[k - 1] >= abs(f[-1]) * prod(c2 - 1 for c2 in squares[k - 1 :])


def test_imaginary_pairs_count_once() -> None:
    """The control: charging both members of each pair is false at ``P_im``.

    The row over the ``2K`` roots of modulus ``c``, counted separately,
    exceeds ``b_k(P_im)``.
    """
    violated = 0
    for c in (2, 3, 4):
        for big_k in (2, 3):
            p_im = _product([[c * c, 0, 1]] * big_k)
            b = _b(p_im)
            for k in range(1, big_k + 1):
                violated += b[k - 1] < (c - 1) ** (2 * big_k - k + 1)
    assert violated


# Roots at arbitrary angles (prop:rowone, item 1).

#: Gaussian integers of integer modulus: ``(a, b, |a + bi|)``.
PYTHAGOREAN = [(3, 4, 5), (4, 3, 5), (5, 12, 13), (12, 5, 13), (8, 15, 17), (0, 2, 2)]


def test_first_row_at_any_angle() -> None:
    """``b_1(F) >= |f_D| prod_j (rho_j - 1)`` over all ``2K`` conjugate roots."""
    rng = random.Random(SEED + 2)
    for _ in range(200):
        pairs = [rng.choice(PYTHAGOREAN) for _ in range(rng.randint(1, 3))]
        f = _mul(
            _product([[a * a + b * b, -2 * a, 1] for a, b, _ in pairs]),
            _cofactor(rng),
        )
        assert _b(f)[0] >= abs(f[-1]) * prod((rho - 1) ** 2 for *_, rho in pairs)


# Several annuli (lem:central, lem:tropcount, thm:annuli, cor:annuli,
# thm:fixedgap, prop:annulisharp, prop:rowsneedn, prop:gaptwo).


def _pair(a: int, b: int) -> Poly:
    """``(x - a - bi)(x - a + bi)``."""
    return [a * a + b * b, -2 * a, 1]


def _central(f: Poly, r: Fraction) -> list[int]:
    """Every central index: the positions maximizing ``|f_i| r^i``."""
    terms = [abs(c) * r**i for i, c in enumerate(f)]
    top = max(terms)
    return [i for i, t in enumerate(terms) if t == top]


def _central_bound(f: Poly, y: int, r: Fraction, moduli: list[int]) -> Fraction:
    """The right side of ``lem:central`` for ``A`` the roots of these moduli."""
    big_d = len(f) - 1
    return (
        Fraction(abs(f[-1]), 2)
        * r ** (big_d - y - len(moduli))
        * prod(max(r, Fraction(rho, 2)) for rho in moduli)
    )


_RADII = [Fraction(1), Fraction(3, 2), Fraction(2), Fraction(7, 2), 6, 13, 40]


def test_central_index() -> None:
    """``lem:central`` at every central index, for all prescribed roots and for
    one pair of them."""
    rng = random.Random(SEED + 11)
    for _ in range(200):
        pairs = [rng.choice(PYTHAGOREAN) for _ in range(rng.randint(1, 3))]
        f = _mul(_product([_pair(a, b) for a, b, _ in pairs]), _cofactor(rng))
        every = [rho for *_, rho in pairs for _ in range(2)]
        for r in map(Fraction, _RADII):
            for y in _central(f, r):
                assert abs(f[y]) > _central_bound(f, y, r, every)
                assert abs(f[y]) > _central_bound(f, y, r, every[:2])


def test_central_index_control() -> None:
    """Without its two factors ``2`` the lemma would put the central term above
    the Jensen mean; ``(x + 2)(2x - 1)`` refutes that at ``r = 1``."""
    f = _mul([2, 1], [-1, 2])
    assert f == [-2, 3, 2]
    (y,) = _central(f, Fraction(1))
    assert abs(f[y]) > _central_bound(f, y, Fraction(1), [2])
    assert abs(f[y]) < abs(f[-1]) * max(1, 2)


def _count_criterion(n: int, kappa: int, x: Fraction) -> bool:
    """The hypothesis of ``lem:tropcount`` at ``x = r/T``."""
    tail = sum(Fraction(comb(n, m)) * x**m for m in range(n - kappa + 1, n + 1))
    return tail < (1 - x) ** n


def _deficit(c100: int, n: int) -> int:
    """``floor(c n)`` for ``c = c100/100``: the most ``lem:tropcount`` lets the
    count fall short of ``n`` at ``T >= 3r`` (``c = 0.82``) or ``T >= 27r``
    (``c = 0.13``)."""
    return c100 * n // 100


def test_count_at_a_distance() -> None:
    """``lem:tropcount``: ``n`` zeros of modulus ``>= T`` put every central
    index at ``r`` at least ``kappa`` below the top whenever the criterion
    holds, in particular ``n`` at ``r = T/(3n)``, ``n/2`` at ``r = T/6``,
    ``n - floor(0.82 n)`` at ``T/3`` and ``n - floor(0.13 n)`` at ``T/27``.

    The last two come from the exact inequalities ``16^0.82 > 19/2`` and
    ``4^0.13 > 31/26`` behind the Chernoff step, and the criterion itself is
    checked exactly for ``n <= 120``."""
    assert 16**82 * 2**100 > 19**100 and 4**13 * 26**100 > 31**100
    for n in range(1, 121):
        assert _count_criterion(n, n - _deficit(82, n), Fraction(1, 3))
        assert _count_criterion(n, n - _deficit(13, n), Fraction(1, 27))
    rng = random.Random(SEED + 12)
    for _ in range(200):
        pairs = [rng.choice(PYTHAGOREAN) for _ in range(rng.randint(1, 3))]
        f = _mul(_product([_pair(a, b) for a, b, _ in pairs]), _cofactor(rng))
        n, big_t = 2 * len(pairs), min(rho for *_, rho in pairs)
        assert _count_criterion(n, n, Fraction(1, 3 * n))
        assert _count_criterion(n, -(-n // 2), Fraction(1, 6))
        for den in (3 * n, 27, 6, 4, 3, 2):
            r = Fraction(big_t, den)
            kappa = max(k for k in range(n + 1) if _count_criterion(n, k, r / big_t))
            if den == 3 * n:
                assert kappa == n
            if den == 6:
                assert 2 * kappa >= n
            if den == 3:
                assert kappa >= n - _deficit(82, n)
            if den == 27:
                assert kappa >= n - _deficit(13, n)
            assert all(len(f) - 1 - y >= kappa for y in _central(f, r))


def test_count_needs_distance() -> None:
    """The control: at a constant distance the full count fails, and at a
    distance ratio below ``1`` so does the half count.  ``(x - 10)^12`` has
    ``12`` zeros of modulus ``10`` but a positive central index at ``10/11``,
    fewer than ``12`` positions above it at ``10/6``, and fewer than ``6`` at
    ``20``; at ``10/36`` the count is full.  At ``10/3`` it falls short by
    ``3``, more than the ``floor(0.13 n)`` allowed at ``T/27``."""
    f = _product([[-10, 1]] * 12)
    assert all(len(f) - 1 - y < 12 for y in _central(f, Fraction(10, 11)))
    assert all(6 <= len(f) - 1 - y < 12 for y in _central(f, Fraction(10, 6)))
    assert all(len(f) - 1 - y < 6 for y in _central(f, Fraction(20)))
    assert all(len(f) - 1 - y >= 12 for y in _central(f, Fraction(10, 36)))
    # At ``T/3`` the count falls short by 3, within ``floor(0.82 * 12)`` but not
    # within the ``floor(0.13 * 12)`` allowed only from ``T/27`` on.
    (y,) = _central(f, Fraction(10, 3))
    assert 12 - (len(f) - 1 - y) == 3 > _deficit(13, 12)


def _annuli(rng: random.Random, gap: int) -> list[list[tuple[int, int, int]]]:
    """Pairs in ``S`` annuli, ``T_a`` above ``3 n_a (3 U_(a-1) + 1)`` if
    ``gap == 0`` (so ``r_a = 3 U_(a-1) + 1`` has ``k_a = n_a``), else above
    ``gap * U_(a-1)``."""
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    annuli = [[rng.choice(small) for _ in range(rng.randint(1, 2))]]
    for _ in range(rng.randint(1, 2)):
        annuli.append([rng.choice(small)])
    for a in range(1, len(annuli)):
        n_a = 2 * sum(len(ann) for ann in annuli[a:])
        upper = max(p[2] for p in annuli[a - 1])
        need = 3 * n_a * (3 * upper + 1) if gap == 0 else gap * upper
        c = need // 5 + 1  # scale (3, 4, 5)-type pairs past ``need``
        annuli[a] = [(c * x, c * y, c * rho) for x, y, rho in annuli[a]]
        assert min(p[2] for p in annuli[a]) > need
    return annuli


def test_annuli_exact_counts() -> None:
    """``thm:annuli`` with ``k_a = n_a`` and ``cor:annuli`` item 1: positions,
    counts, values, rows and mass, at separation ``9 n_a``."""
    rng = random.Random(SEED + 13)
    for _ in range(60):
        annuli = _annuli(rng, 0)
        f = _mul(
            _product([_pair(a, b) for ann in annuli for a, b, _ in ann]),
            _cofactor(rng),
        )
        big_d, lead = len(f) - 1, abs(f[-1])
        moduli = [[rho for *_, rho in ann for _ in range(2)] for ann in annuli]
        big_s = len(annuli)
        bounds = [
            Fraction(lead, 2) * prod(Fraction(rho, 2) for m in moduli[a:] for rho in m)
            for a in range(big_s)
        ]
        radii = [Fraction(1)] + [
            Fraction(3 * max(moduli[a - 1]) + 1) for a in range(1, big_s)
        ]
        for pick in (min, max):
            ys = [pick(_central(f, r)) for r in radii]
            assert ys == sorted(set(ys)) and ys[-1] < big_d
            for a in range(big_s):
                n_a = sum(map(len, moduli[a:]))
                assert a == 0 or big_d - ys[a] >= n_a
                assert abs(f[ys[a]]) > bounds[a]
        b = _b(f)
        for k in range(1, big_s + 1):
            assert b[k - 1] > bounds[k - 1]
        mass = Fraction(lead ** (big_s + 1), 2**big_s) * prod(
            Fraction(rho, 2) ** (s + 1) for s, m in enumerate(moduli) for rho in m
        )
        assert _mass(f) >= mass


def test_annuli_ratio() -> None:
    """``thm:annuli`` at the separation ``9`` alone: ``D - y_a >= k_a`` and
    ``|f_(y_a)| > B_a`` with the power ``r_a^(k_a - n_a)``.

    Control: ``k_a = n_a`` is not automatic there.  With a zero at ``4`` and
    twelve at ``400``, the central index at the admissible ``r_2 = 100`` has
    fewer than ``12`` positions above it.
    """
    rng = random.Random(SEED + 14)
    for _ in range(60):
        annuli = _annuli(rng, 10)
        f = _mul(
            _product([_pair(a, b) for ann in annuli for a, b, _ in ann]),
            _cofactor(rng),
        )
        big_d, lead = len(f) - 1, abs(f[-1])
        moduli = [[rho for *_, rho in ann for _ in range(2)] for ann in annuli]
        big_s = len(annuli)
        for a in range(1, big_s):
            r = Fraction(3 * max(moduli[a - 1]) + 1)
            low = min(moduli[a])
            assert r < Fraction(low, 3)
            kappa = max(k for k in range(64) if 3 * k * r <= low)
            n_a = sum(map(len, moduli[a:]))
            k_a = min(n_a, max(kappa, big_s - a))
            bound = (
                Fraction(lead, 2)
                * r ** (k_a - n_a)
                * prod(Fraction(rho, 2) for m in moduli[a:] for rho in m)
            )
            for y in _central(f, r):
                assert big_d - y >= k_a
                assert abs(f[y]) > bound
    f = _mul([-4, 1], _product([[-400, 1]] * 12))
    assert all(len(f) - 1 - y < 12 for y in _central(f, Fraction(100)))


def _fixed_gap_annuli(rng: random.Random) -> list[list[int]]:
    """Moduli (each twice, a conjugate pair) in ``S`` annuli, each ``T_a`` just
    above ``81 U_(a-1)``; the top annulus may repeat one pair many times."""
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    annuli = [[rng.choice(small) for _ in range(rng.randint(1, 2))]]
    for _ in range(rng.randint(1, 2)):
        annuli.append([rng.choice(small)] * rng.randint(1, 7))
    for a in range(1, len(annuli)):
        upper = max(p[2] for p in annuli[a - 1])
        c = (81 * upper + 30) // min(p[2] for p in annuli[a]) + 1
        annuli[a] = [(c * x, c * y, c * rho) for x, y, rho in annuli[a]]
    return annuli


def _fixed_gap_positions(f: Poly, moduli: list[list[int]]) -> bool:
    """The positions of the proof of ``thm:fixedgap``, at ``r^- = 3 U_(a-1) + 1``
    and ``r^+ = T_a/3``, ordered, counted and charged as there; returns whether
    some central index at ``T_a/3`` has fewer than ``n_a`` positions above it."""
    big_d, lead = len(f) - 1, abs(f[-1])
    big_s = len(moduli)
    for a in range(1, big_s):
        assert min(moduli[a]) > 81 * max(moduli[a - 1])
    charge = [
        Fraction(lead, 2) * prod(Fraction(rho, 2) for m in moduli[a:] for rho in m)
        for a in range(big_s)
    ]
    y1 = max(_central(f, Fraction(1)))
    positions = [y1]
    assert abs(f[y1]) > charge[0]
    short = False
    for a in range(1, big_s):
        n_a = sum(map(len, moduli[a:]))
        lo = Fraction(3 * max(moduli[a - 1]) + 1)
        hi = Fraction(min(moduli[a]), 3)
        assert hi > 9 * lo
        y_lo, y_hi = max(_central(f, lo)), max(_central(f, hi))
        assert y_lo > positions[-1]
        assert n_a - (big_d - y_hi) <= _deficit(82, n_a)
        assert n_a - (big_d - y_lo) <= _deficit(13, n_a)
        ys = sorted({y_lo, y_hi})
        if len(ys) == 1:
            assert big_d - ys[0] >= n_a
            assert abs(f[ys[0]]) > charge[a]
        else:
            value = abs(f[ys[0]] * f[ys[1]])
            assert value > charge[a] * Fraction(lead, 2) * 2**n_a
        short |= big_d - ys[-1] < n_a
        positions += ys
    assert positions[-1] < big_d
    return short


def _fixed_gap_bound(f: Poly, moduli: list[list[int]]) -> Fraction:
    """``exp`` of the right side of ``thm:fixedgap``."""
    lead, big_s = abs(f[-1]), len(moduli)
    return Fraction(lead ** (big_s + 1), 2**big_s) * prod(
        Fraction(rho, 2) ** (s + 1) for s, m in enumerate(moduli) for rho in m
    )


def _cross_term_bound(moduli: list[list[int]]) -> Fraction:
    """``exp sum_i i log(rho_(i)/3)`` over all the prescribed moduli in
    increasing order: the real bound with its square and cross terms, which
    ``prop:annulisharp`` shows false at complex roots."""
    rhos = sorted(rho for m in moduli for rho in m)
    return prod(Fraction(rho, 3) ** i for i, rho in enumerate(rhos, 1))


def test_fixed_gap() -> None:
    """``thm:fixedgap`` at separation ``81`` on random multiples: the
    positions of its proof are ordered and counted as there, and the mass
    bound holds.

    Control: one central index is not enough.  In some samples the central
    index at ``T_a/3`` has fewer than ``n_a`` positions above it, so
    ``lem:central`` alone charges it less than ``Z_a``; the second position
    makes up the charge.
    """
    rng = random.Random(SEED + 15)
    short = 0
    for _ in range(80):
        annuli = _fixed_gap_annuli(rng)
        f = _mul(
            _product([_pair(a, b) for ann in annuli for a, b, _ in ann]),
            _cofactor(rng),
        )
        moduli = [[rho for *_, rho in ann for _ in range(2)] for ann in annuli]
        short += _fixed_gap_positions(f, moduli)
        assert _mass(f) >= _fixed_gap_bound(f, moduli)
    assert short > 0


def test_fixed_gap_near_extremal() -> None:
    """``thm:fixedgap`` where it is nearly attained: ``prod_s (x^(N_s) +- t_s^(N_s))``
    has its ``N_s`` zeros of modulus exactly ``t_s``, ``t_1 > 3`` and
    ``t_a > 81 t_(a-1) + 27`` (the ``+ 27`` leaves room for the radii
    below), and, the subset sums of the ``N_s`` being distinct, mass
    ``prod_s t_s^(2^(S-1) N_s)``: exactly ``prod_s t_s^((2^(S-1) - s) N_s)
    2^(sum_s s N_s + S)`` times the bound, so within ``N_1 log t_1 + O(D)``
    of it when ``S <= 2``, as the lacunary ``F`` of ``prop:annulisharp`` is.
    The positions of the proof and the mass bound hold on every sample.

    Control: the false bound ``sum_i i log(rho_(i)/3)``, the real one with its
    square and cross terms, fails on ``61`` of the ``80`` samples; the random
    multiples of ``test_fixed_gap``, which clear the true bound by a
    log-margin above ``44``, satisfy it every time.
    """
    rng = random.Random(SEED + 16)
    failures = 0
    for _ in range(80):
        ts = [rng.randint(4, 9)]
        for _ in range(rng.randint(0, 2)):
            ts.append(81 * ts[-1] + rng.randint(28, 60))
        ns = rng.sample(range(1, 9), len(ts))
        while len({sum(c) for c in product(*([0, n] for n in ns))}) < 2 ** len(ns):
            ns = rng.sample(range(1, 9), len(ts))  # distinct subset sums
        f = _product(
            [
                [rng.choice([-1, 1]) * t**n] + [0] * (n - 1) + [1]
                for t, n in zip(ts, ns, strict=True)
            ]
        )
        moduli = [[t] * n for t, n in zip(ts, ns, strict=True)]
        _fixed_gap_positions(f, moduli)
        mass = _mass(f)
        assert mass == prod(
            t ** (2 ** (len(ts) - 1) * n) for t, n in zip(ts, ns, strict=True)
        )
        bound = _fixed_gap_bound(f, moduli)
        assert mass >= bound
        big_s = len(ts)
        excess = prod(
            t ** ((2 ** (big_s - 1) - s) * n)
            for s, (t, n) in enumerate(zip(ts, ns, strict=True), 1)
        )
        assert mass == bound * excess * 2 ** (
            sum(s * n for s, n in enumerate(ns, 1)) + big_s
        )
        failures += mass < _cross_term_bound(moduli)
    assert failures > 40


def _lacunary(ns: list[int], ts: list[int]) -> Poly:
    """``prop:annulisharp`` item 1: ``sum_a c_a x^(p_a)``."""
    f = [0] * (sum(ns) + 1)
    for a in range(len(ns) + 1):
        f[sum(ns[:a])] = prod(t**n for t, n in zip(ts[a:], ns[a:], strict=True))
    return f


def _dominant(f: Poly, v: int, r: Fraction) -> bool:
    """Rouche at ``|z| = r``: the term ``v`` beats all others together."""
    terms = [abs(c) * r**i for i, c in enumerate(f)]
    return terms[v] > sum(terms) - terms[v]


@pytest.mark.parametrize(
    ("ns", "ts"),
    [([4, 4], [10, 177147 * 10 + 1]), ([1, 2, 3], [10, 3000, 10**6])],
)
def test_annuli_sharp(ns: list[int], ts: list[int]) -> None:
    """``prop:annulisharp`` item 1: exact Rouche certificates put ``N_s`` zeros
    in ``(t_s/4, 4 t_s)``, and ``Lambda = sum_s s N_s log t_s`` exactly.

    Control: the real cross term ``K_1 K_2 log T_2`` exceeds the mass.
    """
    f = _lacunary(ns, ts)
    assert f[-1] == 1
    ys = [sum(ns[:a]) for a in range(len(ns) + 1)]
    assert _dominant(f, 0, Fraction(ts[0], 4))
    for a, t in enumerate(ts, start=1):
        assert _dominant(f, ys[a], Fraction(4 * t))
        if a < len(ts):
            assert _dominant(f, ys[a], Fraction(ts[a], 4))
    assert _mass(f) == prod(
        t ** (s * n) for s, (t, n) in enumerate(zip(ts, ns, strict=True), 1)
    )
    big_t2 = Fraction(ts[1], 4)
    violated = _mass(f) < big_t2 ** (ns[0] * ns[1])
    assert violated == (ns == [4, 4])


def test_annuli_sector_control() -> None:
    """``prop:annulisharp`` item 2: ``21`` pairs within ``pi/4`` of the
    imaginary axis in each of two annuli, mass linear in the counts, far below
    the cross term ``t_2^(K_1 K_2)``."""
    delta = Fraction(1, 4)  # in units of pi
    ms, ts = [41, 43], [2, 3]
    ks = []
    for m in ms:
        angles = [Fraction(2 * j + 1, 2 * m) for j in range(2 * m)]
        ks.append(sum(abs(t - Fraction(1, 2)) <= delta for t in angles))
        assert ks[-1] == 2 * (m // 4) + 1
    f = _mul(
        [ts[0] ** (2 * ms[0])] + [0] * (2 * ms[0] - 1) + [1],
        [ts[1] ** (2 * ms[1])] + [0] * (2 * ms[1] - 1) + [1],
    )
    assert _mass(f) == ts[0] ** (4 * ms[0]) * ts[1] ** (4 * ms[1])
    assert _mass(f) <= (ts[0] ** (ks[0] + 1) * ts[1] ** (ks[1] + 1)) ** 8
    assert _mass(f) < ts[1] ** (ks[0] * ks[1])


def _rows_need_n(big_k: int, q: int, lam: int) -> Poly:
    """``(x - q)(x + lam q)^K``: ``prop:rowsneedn`` at ``lam = K``."""
    return _mul([-q, 1], _product([[lam * q, 1]] * big_k))


@pytest.mark.parametrize("big_k", [10, 11, 12])
def test_rows_need_n(big_k: int) -> None:
    """``prop:rowsneedn``: at ``T_2 = n_2 U_1`` the row ``k = 2`` of
    ``cor:annuli`` item 1 fails, ``f_1 = 0`` and ``b_2 < 2^K (Kq)^(K-1)``,
    below the row ``(Kq)^K / 2^(K+1)``; the first row holds.

    Control: the same family at ``T_2 = (9K + 1) U_1``, inside ``cor:annuli``
    item 1, meets the row ``k = 2``, so the check is not blind.
    """
    q = 4**big_k
    f = _rows_need_n(big_k, q, big_k)
    assert f[-1] == 1 and q > 3 and big_k * q > 9 * q  # thm:annuli applies
    assert f[1] == 0
    b = _b(f)
    assert b[1] < 2**big_k * (big_k * q) ** (big_k - 1)
    assert b[1] * 2 ** (big_k + 1) < (big_k * q) ** big_k
    assert b[0] * 2 ** (big_k + 2) > q * (big_k * q) ** big_k
    lam = 9 * big_k + 1
    g = _rows_need_n(big_k, q, lam)
    assert _b(g)[1] * 2 ** (big_k + 1) > (lam * q) ** big_k


# The second row at the separation n (lem:trunc, thm:rowstwo, cor:rowstwo).

Cx = tuple[Fraction, Fraction]  # an exact complex number (re, im)


def _cmul(z: Cx, w: Cx) -> Cx:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def _unit_points() -> list[Cx]:
    """Rational points of the unit circle, from Pythagorean triples."""
    out = set()
    for m in range(1, 6):
        for k in range(m):
            a, b, c = m * m - k * k, 2 * m * k, m * m + k * k
            for sa, sb in product((1, -1), repeat=2):
                out.add((Fraction(sa * a, c), Fraction(sb * b, c)))
                out.add((Fraction(sa * b, c), Fraction(sb * a, c)))
    return sorted(out)


def _truncations(xs: list[Cx], big_m: int) -> list[Cx]:
    """``sum_(k <= m) h_k(xs)`` for ``m = 0, ..., big_m``."""
    w: list[Cx] = [(Fraction(1), Fraction(0))] + [(Fraction(0), Fraction(0))] * big_m
    for x in xs:
        for k in range(1, big_m + 1):
            t = _cmul(x, w[k - 1])
            w[k] = (w[k][0] + t[0], w[k][1] + t[1])
    sums, acc = [], (Fraction(0), Fraction(0))
    for z in w:
        acc = (acc[0] + z[0], acc[1] + z[1])
        sums.append(acc)
    return sums


def test_truncation_real_part() -> None:
    """``lem:trunc``, the step for ``n >= 2``: ``Re tau_M(y) >= 1 - n|y|`` on
    ``|y| <= 1/n``, exactly at rational points of circles, with the convexity
    identity behind it and its equality at ``M = 1``, ``y = -1/n``.

    Control: for ``n = 1`` the real part alone fails, at
    ``y = (9/10)(8 - 15i)/17``, ``M = 4``, which is why that case is handled
    by the modulus."""
    for n, k in product(range(2, 30), range(1, 30)):
        value = n * n * (k + 1) * (k + 2) * (
            1 - Fraction(2 * (n + k), n * (k + 1))
        ) + Fraction((n + k) * (n + k + 1), 1)
        assert value == (n - 1) * ((n - 1) * k * (k + 1) - n) >= 0
    points = _unit_points()
    for n in range(2, 7):
        for rho in (Fraction(1, n), Fraction(9, 10 * n), Fraction(1, 3 * n)):
            for c, s in points:
                y = (rho * c, rho * s)
                re = _truncations([y] * n, 9)
                for big_m in range(1, 10):
                    assert re[big_m][0] >= 1 - n * rho
                if (c, s) == (-1, 0):
                    assert re[1][0] == 1 - n * rho
    y = (Fraction(9, 10) * Fraction(8, 17), Fraction(9, 10) * Fraction(-15, 17))
    assert _truncations([y], 4)[4][0] < 0


def test_truncation_lemma() -> None:
    """``lem:trunc``: ``|sum_(k <= M) h_k(x)| >= 1 - n rho`` for ``|x_i| <= rho
    <= 1/n``, exactly, on seeded points of circles of radius ``rho`` and below.

    Control: ``1 - n rho`` is sharp, so ``1 - (n - 1/2) rho`` is false, at
    ``M = 1`` and ``x_i = -rho``."""
    rng = random.Random(SEED + 31)
    points = _unit_points()
    for _ in range(300):
        n = rng.randint(1, 6)
        rho = Fraction(rng.randint(1, 10), 10 * n)
        xs = []
        for _ in range(n):
            c, s = rng.choice(points)
            r = rho * rng.choice([1, 1, Fraction(1, 2)])
            xs.append((r * c, r * s))
        for z in _truncations(xs, 8):
            assert z[0] ** 2 + z[1] ** 2 >= (1 - n * rho) ** 2
    n, rho = 4, Fraction(1, 10)
    (_, z) = _truncations([(-rho, Fraction(0))] * n, 1)
    assert z == (1 - n * rho, 0) and z[0] < 1 - (n - Fraction(1, 2)) * rho


def _second_row_bound(f: Poly, alpha: int, moduli: list[int]) -> Fraction:
    """The right side of ``thm:rowstwo``, ``T`` the least of the moduli, with
    its two consequences ``lambda / 8`` and ``lambda^2 / 2`` checked below it."""
    n, a = len(moduli), abs(alpha)
    lam = 1 - Fraction(n * a, min(moduli))
    gamma = 1 if n == 1 else (1 - Fraction(a, min(moduli))) ** n
    assert 0 < lam <= 1 and a > 1 and gamma >= max(lam, Fraction(1, 4))
    bound = lam * gamma / 2 * (1 - Fraction(1, a)) * abs(f[-1]) * prod(moduli)
    assert bound >= max(lam / 8, lam**2 / 2) * (1 - Fraction(1, a)) * abs(f[-1]) * prod(
        moduli
    )
    return bound


def test_second_row_at_separation_n() -> None:
    """``thm:rowstwo`` on seeded integer multiples with ``n`` zeros of modulus
    at least ``T`` (real of both signs, or Pythagorean pairs) and a zero
    ``alpha`` with ``1 < |alpha| < T/n``, and on ``(x - q)(x + t)^K`` just past
    ``t = Kq``, where the ratio ``b_2 / prod |beta|`` is ``lambda`` for large
    ``q`` (the remark after the theorem), and at ``n = 1`` with ``|beta|``
    just above ``|alpha|``, where ``lambda`` is small and ``gamma = 1``.

    Control: without the factor ``lambda`` the bound fails, at
    ``t = Kq + 1``."""
    rng = random.Random(SEED + 32)
    for _ in range(300):
        alpha = rng.choice([-1, 1]) * rng.randint(2, 12)
        factors, moduli = [], []
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.5:
                x, y, rho = rng.choice(PYTHAGOREAN[:5])
                factors.append(_pair(x, y))
                moduli += [rho, rho]
            else:
                t = rng.randint(1, 40)
                factors.append([-rng.choice([-1, 1]) * t, 1])
                moduli.append(t)
        n = len(moduli)
        scale = n * abs(alpha) // min(moduli) + rng.randint(1, 3)
        factors = [
            [c * scale ** (len(p) - 1 - i) for i, c in enumerate(p)] for p in factors
        ]
        moduli = [scale * m for m in moduli]
        f = _product([[-alpha, 1], _cofactor(rng), *factors])
        assert all(_divides(p, f) for p in factors)
        assert _b(f)[1] >= _second_row_bound(f, alpha, moduli)
    for alpha, beta in product((2, -3, 7, -40), (1, 2, 5)):
        beta = -(abs(alpha) + beta) if alpha > 0 else abs(alpha) + beta
        for cofactor in ([1], [1, 1], [-2, 0, 1], [3, -1, 0, 1]):
            f = _product([[-alpha, 1], [-beta, 1], cofactor])
            assert _b(f)[1] >= _second_row_bound(f, alpha, [abs(beta)])
    for big_k, q in product((1, 3, 10), (5, 4**10)):
        for t in (big_k * q + 1, 2 * big_k * q):
            f = _mul([-q, 1], _product([[t, 1]] * big_k))
            assert _b(f)[1] >= _second_row_bound(f, q, [t] * big_k)
    q, big_k, lam = 4**10, 10, Fraction(1, 4)
    t = big_k * q / (1 - lam)
    f = _mul([Fraction(-q), Fraction(1)], _product([[t, Fraction(1)]] * big_k))
    assert f[1] == lam * t**big_k == _b(f)[1]
    t = big_k * q + 1
    f = _mul([-q, 1], _product([[t, 1]] * big_k))
    assert _b(f)[1] < Fraction(1, 2) * (1 - Fraction(1, q)) * t**big_k


def _second_row_large(f: Poly, alpha: int, moduli: list[int]) -> Fraction:
    """The right side of ``prop:rowstwolarge``, with ``Gamma <= a/(a-1+lambda)``
    and, for ``a >= 2``, the bound ``lambda (1 - 1/a)^2`` checked below it."""
    n, a, big_t = len(moduli), abs(alpha), min(moduli)
    lam = 1 - Fraction(n * a, big_t)
    big_g = Fraction(big_t, big_t - 1) ** n
    assert 0 < lam <= 1 and big_g <= a / (a - 1 + lam)
    c = min(
        lam * (a - 1) / (big_g * (a - lam)), (a - 1) / (1 + (2 * a - 1) * (big_g - 1))
    )
    if a >= 2:
        assert c >= lam * (1 - Fraction(1, a)) ** 2
    return c * abs(f[-1]) * prod(moduli)


def test_second_row_at_a_large_lower_zero() -> None:
    """``prop:rowstwolarge`` on the multiples of ``test_second_row_at_separation_n``
    and on ``(x - q)(x + t)^K`` with ``t = Kq/(1 - lambda)``, where
    ``b_2 = lambda prod |beta|`` and the ratio to ``lambda (1 - 1/q) prod |beta|``
    is ``q/(q - 1)``, so the constant 1 of the remark is approached.

    Control: that family has ``b_2`` below ``lambda (1 + 1/q) prod |beta|``, so
    no constant above 1 holds, and at ``t = Kq + 1`` the bound of
    ``thm:rowstwo`` without ``lambda`` fails (``test_second_row_at_separation_n``)."""
    rng = random.Random(SEED + 36)
    for _ in range(300):
        alpha = rng.choice([-1, 1]) * rng.randint(2, 12)
        factors, moduli = [], []
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.5:
                x, y, rho = rng.choice(PYTHAGOREAN[:5])
                factors.append(_pair(x, y))
                moduli += [rho, rho]
            else:
                t = rng.randint(1, 40)
                factors.append([-rng.choice([-1, 1]) * t, 1])
                moduli.append(t)
        scale = len(moduli) * abs(alpha) // min(moduli) + rng.randint(1, 3)
        factors = [
            [c * scale ** (len(p) - 1 - i) for i, c in enumerate(p)] for p in factors
        ]
        moduli = [scale * m for m in moduli]
        f = _product([[-alpha, 1], _cofactor(rng), *factors])
        assert _b(f)[1] >= _second_row_large(f, alpha, moduli)
    for big_k, q in product((1, 3, 10), (5, 40, 4**10)):
        for t in (big_k * q + 1, 2 * big_k * q):
            f = _mul([-q, 1], _product([[t, 1]] * big_k))
            assert _b(f)[1] >= _second_row_large(f, q, [t] * big_k)
    for lam in (Fraction(1, 4), Fraction(1, 100)):
        big_k, q = 10, 4**12
        t = big_k * q / (1 - lam)
        f = _mul([Fraction(-q), Fraction(1)], _product([[t, Fraction(1)]] * big_k))
        pi = t**big_k
        assert _b(f)[1] == lam * pi
        assert _b(f)[1] >= lam * (1 - Fraction(1, q)) ** 2 * pi
        assert _b(f)[1] / (lam * (1 - Fraction(1, q)) * pi) == Fraction(q, q - 1)
        assert _b(f)[1] < lam * (1 + Fraction(1, q)) * pi


def _second_row_half_q(n: int, lam: Fraction, a: Fraction) -> list[Fraction]:
    """``Q_2, Q_0, Q_1`` of ``prop:rowstwohalf`` at ``T = n a/(1 - lambda)``."""
    big_t = n * a / (1 - lam)
    rho = a / big_t
    g = (1 - rho) ** -n
    big_g = (1 - 1 / big_t) ** -n
    r = g - 1 - n * rho
    w = lam * (1 - 1 / a)
    return [
        w * big_g,
        lam * g / a + w * (big_g - 1),
        (1 - lam) * (a - 1 + lam + r) / a + w * big_g,
    ]


def test_second_row_constant_half() -> None:
    """``prop:rowstwohalf``: ``b_2 >= (lambda/2)(1 - 1/|alpha|) |f_D| prod |beta|``
    on the seeded multiples of ``test_second_row_at_separation_n`` and on
    multiples with a rational lower zero ``alpha = 1 + 1/m`` close to 1; the
    three quantities ``Q`` of its proof at most 2 on a rational grid, and the
    polynomial identity behind ``Q_1 <= 2``.

    Control: ``Q_1`` comes within ``1/100`` of 2 at ``n = 2``, ``lambda``
    small and ``|alpha|`` close to 1, so the proof gives no constant above
    1/2; and ``(x - q)(x + t)^K`` with ``t = Kq/(1 - lambda)`` has
    ``b_2 < lambda (1 + 1/q) prod |beta|``, so no constant above 1 holds."""
    rng = random.Random(SEED + 38)
    for _ in range(300):
        if rng.random() < 0.5:
            alpha = Fraction(rng.choice([-1, 1]) * rng.randint(2, 12))
        else:
            m = rng.randint(1, 20)
            alpha = rng.choice([-1, 1]) * Fraction(m + 1, m)
        factors, moduli = [], []
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.5:
                x, y, rho = rng.choice(PYTHAGOREAN[:5])
                factors.append(_pair(x, y))
                moduli += [rho, rho]
            else:
                t = rng.randint(1, 40)
                factors.append([-rng.choice([-1, 1]) * t, 1])
                moduli.append(t)
        n, a = len(moduli), abs(alpha)
        scale = int(n * a) // min(moduli) + rng.randint(1, 3)
        factors = [_scaled(p, scale) for p in factors]
        moduli = [scale * r for r in moduli]
        lam = 1 - n * a / min(moduli)
        assert 0 < lam <= 1
        f = _product([[-alpha, Fraction(1)], _cofactor(rng), *factors])
        bound = lam / 2 * (1 - 1 / a) * abs(f[-1]) * prod(moduli)
        assert _b(f)[1] >= bound
    for n in range(2, 7):
        for lam in (
            Fraction(1, 1000),
            Fraction(1, 10),
            Fraction(1, 2),
            Fraction(9, 10),
        ):
            for a in (
                Fraction(1001, 1000),
                Fraction(11, 10),
                Fraction(2),
                Fraction(50),
            ):
                assert max(_second_row_half_q(n, lam, a)) <= 2
    for lam in (Fraction(k, 20) for k in range(1, 21)):
        g = 4 / (1 + lam) ** 2
        lhs = (1 + lam) ** 2 * (2 - lam - (1 - lam) * (g - 2 + 2 * lam))
        assert lhs == lam * (7 - 4 * lam - lam**2 + 2 * lam**3) >= 0
    q_1 = _second_row_half_q(2, Fraction(1, 10**4), Fraction(10001, 10000))[2]
    assert 2 - Fraction(1, 100) < q_1 <= 2
    big_k, q, lam = 10, 4**12, Fraction(1, 4)
    t = big_k * q / (1 - lam)
    f = _mul([Fraction(-q), Fraction(1)], _product([[t, Fraction(1)]] * big_k))
    assert _b(f)[1] < lam * (1 + Fraction(1, q)) * t**big_k


def test_rows_for_two_annuli() -> None:
    """``cor:rowstwo`` for ``S = 2``: rows ``k = 1, 2`` and the mass of
    ``cor:annuli`` item 1 at ``T_2`` just above ``max(9, n_2 + 1) U_1``, on
    seeded multiples with pairs below and real zeros and pairs above; and the
    ``C``-form ``b_2 >= (1 - 1/C)^2 / 3 * |f_D| prod |beta|``.

    Control: ``(x - q)(x + Kq)^K`` at ``T_2 = n_2 U_1`` misses the row
    (``prop:rowsneedn``, ``test_rows_need_n``), while ``T_2 = (K + 1) q + 1``
    meets it."""
    assert all((9 - n) ** 2 * 2 ** (n + 1) >= 256 for n in range(1, 9))
    assert all(2 ** (n + 1) >= 3 * (n + 1) ** 2 for n in range(8, 200))
    rng = random.Random(SEED + 33)
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    for _ in range(80):
        lower = [rng.choice(small) for _ in range(rng.randint(1, 2))]
        upper_u = max(rho for *_, rho in lower)
        upper: list[tuple[Poly, int]] = []
        for _ in range(rng.randint(1, 6)):
            x, y, rho = rng.choice(small)
            upper.append((_pair(x, y), rho) if rng.random() < 0.5 else ([rho, 1], rho))
        n_2 = sum(len(p) - 1 for p, _ in upper)
        scale = max(9, n_2 + 1) * upper_u // min(rho for _, rho in upper) + 1
        upper = [
            ([c * scale ** (len(p) - 1 - i) for i, c in enumerate(p)], scale * rho)
            for p, rho in upper
        ]
        big_t2 = min(rho for _, rho in upper)
        assert big_t2 > max(9, n_2 + 1) * upper_u
        f = _mul(
            _product([_pair(x, y) for x, y, _ in lower] + [p for p, _ in upper]),
            _cofactor(rng),
        )
        lead = abs(f[-1])
        up = [rho for p, rho in upper for _ in range(len(p) - 1)]
        low = [rho for *_, rho in lower for _ in range(2)]
        b1 = Fraction(lead, 2) * prod(Fraction(r, 2) for r in low + up)
        b2 = Fraction(lead, 2) * prod(Fraction(r, 2) for r in up)
        b = _b(f)
        assert b[0] > b1 and b[1] > b2
        assert _mass(f) >= lead * b1 * b2
        big_c = Fraction(big_t2, n_2 * upper_u)
        assert b[1] >= (1 - 1 / big_c) ** 2 / 3 * lead * prod(up)
    for big_k in (10, 11, 12):
        q = 4**big_k
        f = _mul([-q, 1], _product([[(big_k + 1) * q + 1, 1]] * big_k))
        assert _b(f)[1] * 2 ** (big_k + 1) > ((big_k + 1) * q + 1) ** big_k


# Rows for three or more annuli (lem:rowsbelow, thm:rowsk, cor:rowsall,
# prop:rowslower).


def _scaled(p: Poly, s: int) -> Poly:
    """``s^deg p * p(x / s)``: the zeros of ``p`` times ``s``."""
    return [c * s ** (len(p) - 1 - i) for i, c in enumerate(p)]


def _annuli_rows(
    rng: random.Random, gap: Callable[[int, int], int], sizes: list[int]
) -> tuple[Poly, list[list[int]]]:
    """A multiple of zeros in ``len(sizes)`` annuli, real of both signs or
    Pythagorean pairs, the ``a``-th annulus holding ``sizes[a - 1]`` factors,
    scaled so that ``T_a > gap(a, n_a) U_(a-1)``; returns it with the moduli
    per annulus."""
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    groups: list[list[tuple[Poly, int]]] = []
    for size in sizes:
        group = []
        for _ in range(size):
            x, y, rho = rng.choice(small)
            if rng.random() < 0.5:
                group.append((_pair(x, y), rho))
            else:
                group.append(([rng.choice([-1, 1]) * rho, 1], rho))
        groups.append(group)
    counts = [sum(len(p) - 1 for p, _ in g) for g in groups]
    scale, upper_u, out = 1, 0, []
    for a, group in enumerate(groups):
        if a:
            n_a = sum(counts[a:])
            least = min(rho for _, rho in group)
            scale = gap(a + 1, n_a) * upper_u // least + 1
        group = [(_scaled(p, scale), scale * rho) for p, rho in group]
        out.append(group)
        upper_u = max(rho for _, rho in group)
    moduli = [[rho for p, rho in g for _ in range(len(p) - 1)] for g in out]
    f = _mul(_product([p for g in out for p, _ in g]), _cofactor(rng))
    return f, moduli


def _row(f: Poly, moduli: list[list[int]], k: int) -> Fraction:
    """The row ``k`` of ``cor:annuli`` item 1: ``|f_D|/2 prod |beta|/2``."""
    up = [r for g in moduli[k - 1 :] for r in g]
    return Fraction(abs(f[-1]), 2) * prod(Fraction(r, 2) for r in up)


def _rows_k_epsilon(n: int, lam: Fraction, gamma: Fraction, xi: Fraction) -> Fraction:
    """``2 eps / (1 - 1/|alpha|)`` in ``thm:rowsk``."""
    return gamma * (lam * (1 - 2 * xi) - (1 - lam) * xi / (1 - xi))


def _rows_all_margin(c: int, n: int) -> Fraction:
    """``gamma V - (27/26) 2^(-n)`` in the proof of ``cor:rowsall``, with the
    separation ``n_a + c`` in place of ``n_a + 9``."""
    m = n + c
    return _rows_k_epsilon(
        n, Fraction(c, m), (1 - Fraction(1, m)) ** n, Fraction(3, m + 1)
    ) - Fraction(27, 26 * 2**n)


def test_rows_positions_below() -> None:
    """``lem:rowsbelow``: the row ``k`` needs the factor ``9 n_k`` only at the
    ``k``-th separation, on seeded multiples with three annuli, the other
    separation just above ``9``.

    Control: the family of ``prop:rowsneedn`` with a third annulus far above
    misses the row ``2`` at ``T_2 = n_2 U_1``, so the check is not blind."""
    rng = random.Random(SEED + 34)
    for _ in range(40):
        k = rng.choice([2, 3])
        sizes = [rng.randint(1, 2), rng.randint(1, 3), rng.randint(1, 3)]
        f, moduli = _annuli_rows(rng, lambda a, n, k=k: 9 * n if a == k else 9, sizes)
        b = _b(f)
        assert b[k - 1] > _row(f, moduli, k)
    big_k, q = 10, 4**10
    f = _mul(_rows_need_n(big_k, q, big_k), [-(10**40), 1])
    moduli = [[q], [big_k * q] * big_k, [10**40]]
    assert _b(f)[1] < _row(f, moduli, 2)


def test_rows_at_separation_n_plus_nine() -> None:
    """``thm:rowsk`` and ``cor:rowsall``: the bound
    ``b_k >= min(2^(-n-1), eps) |f_D| prod |beta|`` at a zero of the
    ``(k-1)``-st annulus, and every row and the mass of ``cor:annuli`` item 1
    at ``T_a`` just above ``(n_a + 9) U_(a-1)``, on seeded multiples with three
    and four annuli; and the numbers in the proof of ``cor:rowsall``.

    Control: with ``n_a + 8`` in place of ``n_a + 9`` the inequality of that
    proof fails at ``n = 2``, and with ``n_a + 9`` at ``n = 1``, which is why
    ``n_k = 1`` is left to ``lem:rowsbelow``."""
    for n in range(2, 300):
        assert _rows_all_margin(9, n) > 0
    for n in range(4, 300):
        m = n + 9
        v = Fraction(6 * m * m - 39 * m + 117, m * (m + 1) * (m - 2))
        assert v == _rows_k_epsilon(n, Fraction(9, m), Fraction(1), Fraction(3, m + 1))
        assert v >= Fraction(3, m) and 3 / (2.7183 * m) >= 27 / 26 / 2**n
    assert _rows_all_margin(8, 2) < 0 and _rows_all_margin(9, 1) < 0
    rng = random.Random(SEED + 35)
    for _ in range(40):
        sizes = [rng.randint(1, 2) for _ in range(rng.choice([3, 4]))]
        f, moduli = _annuli_rows(rng, lambda a, n: n + 9, sizes)
        b = _b(f)
        rows = [_row(f, moduli, k) for k in range(1, len(sizes) + 1)]
        assert all(b[k] > rows[k] for k in range(len(sizes)))
        assert _mass(f) >= abs(f[-1]) * prod(rows)
        for k in range(3, len(sizes) + 1):
            up = [r for g in moduli[k - 1 :] for r in g]
            n, big_t = len(up), min(up)
            xi = Fraction(3 * max(moduli[k - 3]), min(moduli[k - 2]))
            for a in set(moduli[k - 2]):
                lam = 1 - Fraction(n * a, big_t)
                gamma = (1 - Fraction(a, big_t)) ** n
                eps = _rows_k_epsilon(n, lam, gamma, xi) / 2 * (1 - Fraction(1, a))
                assert eps > Fraction(1, 2 ** (n + 1)) or n == 1
                bound = min(Fraction(1, 2 ** (n + 1)), eps) * abs(f[-1]) * prod(up)
                assert b[k - 1] >= bound


def _rows_lower_zeros(h: Fraction, big_k: int, p: int) -> tuple[int, int, int]:
    """``q_1, q_2, t`` of ``prop:rowslower``, integers when ``v^2 | p``."""
    q_1 = 2 * h * (big_k + h) * p
    q_2 = big_k * (big_k + 1 + 2 * h) * p
    t = (big_k + h) * q_2
    assert q_1.denominator == q_2.denominator == t.denominator == 1
    return int(q_1), int(q_2), int(t)


def _rows_lower(h: Fraction, big_k: int, p: int, q_1: int | None = None) -> Poly:
    """``prop:rowslower``: ``(x - q_1)(x - q_2)(x + t)^K``."""
    q, q_2, t = _rows_lower_zeros(h, big_k, p)
    q_1 = q if q_1 is None else q_1
    return _product([[-q_1, 1], [-q_2, 1]] + [[t, 1]] * big_k)


@pytest.mark.parametrize(
    ("h", "big_k"),
    [(1, 18), (1, 25), (2, 36), (3, 54), (Fraction(1, 3), 12), (Fraction(2, 5), 20)],
)
def test_row_three_needs_the_lower_separation(h: int | Fraction, big_k: int) -> None:
    """``prop:rowslower``: at ``T_3 = (n_3 + h) U_2`` and
    ``9 U_1 < T_2 < (n_2 / (2h) + 1) U_1`` the row ``k = 3`` fails,
    ``f_2 = 0`` and ``b_3 <= 4 t^K / q_2 < t^K / 2^(K+1)``; for ``h < 1/2``
    also ``T_2 > (n_2 + h) U_1``, so both separations exceed ``n_a + h``.

    Control: the same ``q_2`` and ``t`` with ``q_1 = 1``, far below, meet the
    row, and so does ``q_1 = 1`` at ``T_3`` just above ``(n_3 + 9) U_2``
    (``cor:rowsall``)."""
    h = Fraction(h)
    p = h.denominator**2 * 2**big_k
    q_1, q_2, t = _rows_lower_zeros(h, big_k, p)
    f = _rows_lower(h, big_k, p)
    assert f[-1] == 1 and q_1 > 3 and big_k >= max(9, 18 * h)
    assert t > 9 * q_2 and q_2 > 9 * q_1
    assert t == (big_k + h) * q_2
    assert 9 * q_1 < q_2 < (Fraction(big_k + 1, 2 * h) + 1) * q_1
    if h < Fraction(1, 2):
        assert (1 - 2 * h) * big_k**2 >= 1 and q_2 > (big_k + 1 + h) * q_1
    assert f[2] == 0
    assert all(abs(c) * q_2 <= 4 * t**big_k for c in f[2:-1])
    assert _b(f)[2] * q_2 <= 4 * t**big_k < q_2 * t**big_k // 2 ** (big_k + 1)
    g = _rows_lower(h, big_k, p, q_1=1)
    assert _b(g)[2] * 2 ** (big_k + 1) > t**big_k
    s = _product([[-1, 1], [-q_2, 1]] + [[(big_k + 10) * q_2, 1]] * big_k)
    assert _b(s)[2] * 2 ** (big_k + 1) > ((big_k + 10) * q_2) ** big_k
    # K >= 9 is needed: at h = 1/6 the bound 18h allows K = 3, where
    # T_3 = (K + h) U_2 < 9 U_2 and thm:annuli does not apply.
    small_h = Fraction(1, 6)
    _, q_2, t = _rows_lower_zeros(small_h, 3, 36 * 8)
    assert 3 >= 18 * small_h and t < 9 * q_2


def _pair_margin(
    n: int, rho: Fraction, s: Fraction, q: Fraction, x_0: Fraction
) -> Fraction:
    """``Xi - nu`` of ``thm:rowspair``, after checking its two side conditions."""
    theta = Fraction(1, 2 ** (n + 1))
    lam, gamma, gamma_1 = 1 - n * rho, (1 - rho) ** n, (1 - s * rho) ** n
    assert theta < gamma and 2 * gamma_1 - 1 > q / (1 - q)
    e = 3 * theta / (2 * gamma * (1 - x_0) * (1 - theta / gamma))
    eta = (1 - gamma_1) / (2 * gamma_1 - 1)
    kappa = (1 + e) / (2 * gamma_1 - 1 - q / (1 - q))
    delta = max(n * (n + 1) * rho**2 / 2, s * (1 / gamma - 1))
    xi = min(lam * (1 - s) - s * delta, 1 - s / gamma)
    nu = s / gamma * (
        eta + kappa * q * s / (1 - q * s) + kappa * q / ((1 - q) * (2 * gamma_1 - 1))
    ) + e * (1 + Fraction(3, 2) / (2 * gamma_1 - 1))
    return xi - nu


def _pair_phi(
    n: int, rho: Fraction, s: Fraction, q: Fraction, x_0: Fraction
) -> list[Fraction] | None:
    """The three values of ``Phi`` in ``thm:rowspair``, or ``None`` where its
    side conditions fail."""
    theta = Fraction(1, 2 ** (n + 1))
    lam, gamma, gamma_1 = 1 - n * rho, (1 - rho) ** n, (1 - s * rho) ** n
    if not (theta < gamma and 2 * gamma_1 - 1 > q / (1 - q)):
        return None
    e = 3 * theta / (2 * gamma * (1 - x_0) * (1 - theta / gamma))
    eta = (1 - gamma_1) / (2 * gamma_1 - 1)
    kappa = (1 + e) / (2 * gamma_1 - 1 - q / (1 - q))

    def phi(sigma: Fraction, tau: Fraction, omega: Fraction) -> Fraction:
        slope = (
            omega * eta
            + omega * kappa * q / ((1 - q) * (2 * gamma_1 - 1))
            + 3 * e * gamma / (2 * (2 * gamma_1 - 1))
        )
        return (
            sigma * (1 - omega)
            - omega * tau
            - (sigma + tau) * slope
            - omega * kappa * q * s / (gamma * (1 - q * s))
            - e
        )

    return [
        phi(Fraction(1), 1 / gamma - 1, s),
        phi(lam, n * (n + 1) * rho**2 / 2, s),
        phi(lam, 1 / gamma - 1 - n * rho, s * s),
    ]


def _pair_at_bounds(
    n: int, g_0: Fraction, g_1: Fraction, g_2: Fraction | None
) -> list[Fraction] | None:
    """``Phi`` at the bounds of ``cor:rowsplusone``: ``rho = 1/g_0``,
    ``s = 1/g_1``, ``q = 3/g_2`` (``q = 0`` for ``k = 3``, ``g_2 = None``)
    and ``x_0 = 3n/(g_0 g_1)``."""
    q = Fraction(0) if g_2 is None else 3 / g_2
    return _pair_phi(n, 1 / g_0, 1 / g_1, q, 3 * n / (g_0 * g_1))


def _sigma_rows(n: int) -> Fraction:
    """``sigma`` of ``cor:rowsplusone`` item 3."""
    if n >= 10:
        return Fraction(n + 1)
    if n >= 3:
        return max(Fraction(9), n + Fraction(3, 2))
    return Fraction(12 if n == 2 else 6)


def _pair_worst(n: int, c: Fraction) -> Fraction:
    """The margin at the bounds of ``cor:rowsplusone``, separation ``n_a + c``."""
    return _pair_margin(
        n, 1 / (n + c), 1 / (n + 1 + c), 3 / (n + 2 + c), Fraction(1, 10)
    )


def test_row_k_at_two_lower_zeros() -> None:
    """``thm:rowspair`` on ``(x - q_1)(x - q_2)(x + t)^K`` of ``prop:rowslower``
    with ``q_1`` swept below ``q_2 / 9``: wherever ``Xi > nu`` at the actual
    ``rho = q_2/t``, ``s = q_1/q_2`` and ``x_0 = K(3q_1 + 1)/t``, the row ``3``
    holds, and ``Xi > nu`` already at ``s = 3 lambda / 2``, close to the
    cancellation at ``s ~ 2 lambda``; each of the three values of ``Phi`` is
    at least ``Xi - nu``, and wherever all three are positive the row holds.

    Control: at the cancelling ``q_1`` the row fails and ``Xi <= nu`` and
    ``min Phi <= 0``, and ``thm:rowsk`` gives nothing there (its
    ``epsilon`` is negative)."""
    big_k, h = 40, Fraction(1)
    p = 2**60
    q_1, q_2, t = _rows_lower_zeros(h, big_k, p)
    rho, lam = Fraction(q_2, t), 1 - big_k * Fraction(q_2, t)
    row = Fraction(t**big_k, 2 ** (big_k + 1))
    positive = positive_phi = 0
    for num in range(1, 110):
        b = q_2 * num // 1000
        args = (
            big_k,
            rho,
            Fraction(b, q_2),
            Fraction(0),
            Fraction(big_k * (3 * b + 1), t),
        )
        margin = _pair_margin(*args)
        phi = _pair_phi(*args)
        assert phi is not None and min(phi) >= margin
        assert 7 * big_k * (3 * b + 1) < 3 * t and 3 * (3 * b + 1) < q_2
        positive += margin > 0
        if min(phi) > 0:
            positive_phi += 1
            f = _product([[-b, 1], [-q_2, 1]] + [[t, 1]] * big_k)
            assert _b(f)[2] > row
    assert positive > 30 and positive_phi >= positive
    s = Fraction(3, 2) * lam
    assert _pair_margin(big_k, rho, s, Fraction(0), 3 * big_k * s * rho) > 0
    f = _rows_lower(h, big_k, p)
    assert _b(f)[2] < row
    s = Fraction(q_1, q_2)
    args = (big_k, rho, s, Fraction(0), big_k * (3 * q_1 + 1) / Fraction(t))
    assert _pair_margin(*args) <= 0
    phi = _pair_phi(*args)
    assert phi is not None and min(phi) <= 0
    assert _rows_k_epsilon(big_k, lam, (1 - rho) ** big_k, 3 * s) < 0


def test_rows_at_separation_n_plus_one() -> None:
    """``cor:rowsplusone``: the finite computation of its proof (the side
    conditions and the three values of ``Phi`` of ``thm:rowspair`` positive at
    the rational bounds, for ``k = 3`` and ``k >= 4``: at ``n_a + 1`` for
    ``10 <= n <= 29``, and for ``k = 3`` from ``n = 7``, and at ``sigma`` of
    item 3 for ``3 <= n <= 9``), the numbers of item 1 for ``30 <= n <= 120``,
    the margin of item 2 at ``c = 11/20`` for large ``n``, and every row and
    the mass at ``T_a`` just above ``sigma(n_a) U_(a-1)`` on seeded multiples
    with three and four annuli, with 1 to 12 or thirty zeros in the top one.

    Control: at ``n_a + 1`` a value of ``Phi`` is negative at ``n = 6`` for
    ``k = 3`` and at ``n = 9`` for ``k >= 4``, where item 1 stops; at
    ``c = 9/20 < 1/2`` the margin is negative for large ``n``, as
    ``prop:rowslower`` requires, and at ``c = 1`` ``Xi - nu`` is negative at
    ``n = 12``."""

    def positive(v: list[Fraction] | None) -> bool:
        return v is not None and min(v) > 0

    for n in range(7, 30):
        g = [Fraction(n + 1), Fraction(n + 2), Fraction(n + 3)]
        assert g[1] >= 9 and g[0] * g[1] > 7 * n
        assert positive(_pair_at_bounds(n, g[0], g[1], None))
        if n >= 10:
            assert positive(_pair_at_bounds(n, *g))
        assert (27 <= n) == (3 * n / (g[0] * g[1]) <= Fraction(1, 10))
    for n in range(3, 10):
        g = [_sigma_rows(n + i) for i in range(3)]
        assert g[0] > n and min(g) >= 9 and g[0] * g[1] > 7 * n
        assert g[0] <= g[1] <= g[2] and g[0] <= min(n + 9, 12)
        assert positive(_pair_at_bounds(n, g[0], g[1], None))
        assert positive(_pair_at_bounds(n, *g))
    assert not positive(_pair_at_bounds(6, Fraction(7), Fraction(8), None))
    assert not positive(_pair_at_bounds(9, Fraction(10), Fraction(11), Fraction(12)))
    for n in range(30, 121):
        rho, s, q = Fraction(1, n + 1), Fraction(1, n + 2), Fraction(3, n + 3)
        gamma, gamma_1 = (1 - rho) ** n, (1 - s * rho) ** n
        theta = Fraction(1, 2 ** (n + 1))
        e = 3 * theta / (2 * gamma * Fraction(9, 10) * (1 - theta / gamma))
        kappa = (1 + e) / (2 * gamma_1 - 1 - q / (1 - q))
        assert 1 / gamma < 3 and 2 * gamma_1 - 1 > Fraction(n, n + 2)
        assert (
            e < Fraction(4, 2**n)
            and kappa < Fraction(6, 5)
            and q * s < Fraction(1, 11 * n)
        )
        assert (n * n - 28 * n - 30) * 2 ** (n - 4) > 2 * n * (n + 1) * (n + 2)
        assert _pair_worst(n, Fraction(1)) > 0
    for n in (400, 800):
        assert _pair_worst(n, Fraction(11, 20)) > 0
        assert _pair_worst(n, Fraction(9, 20)) < 0
    assert _pair_worst(12, Fraction(1)) < 0

    rng = random.Random(SEED + 37)
    for top in [30] * 6 + list(range(1, 13)):
        sizes = [rng.randint(1, 2) for _ in range(rng.choice([2, 3]))] + [top]
        f, moduli = _annuli_rows(rng, lambda a, n: _sigma_rows(n), sizes)
        assert len(moduli[-1]) >= top
        b = _b(f)
        rows = [_row(f, moduli, k) for k in range(1, len(sizes) + 1)]
        assert all(b[k] > rows[k] for k in range(len(sizes)))
        assert _mass(f) >= abs(f[-1]) * prod(rows)


def test_mass_fails_at_separation_two() -> None:
    """``prop:gaptwo``: ``(x - q)(x + t)^2`` with ``t = 2q + 1/(2q + 1)`` has
    ``T_2 > 2 U_1`` and mass below the bound of ``thm:fixedgap``, by the exact
    factor ``t^2 / (128 (3q + 2 delta))``, which grows with ``q``.

    Control: at ``t = 82 q``, inside ``thm:fixedgap``, the bound holds.
    """
    ratios = []
    for q in (97, 1000, 10**6):
        delta = Fraction(1, 2 * q + 1)
        t = 2 * q + delta
        f = _mul([Fraction(-q), Fraction(1)], _mul([t, Fraction(1)], [t, Fraction(1)]))
        assert t > 2 * q and 0 < f[1] < 1
        bound = Fraction(q, 2) * (t / 2) ** 4 / 4  # exp of the bound, S = 2
        assert _mass(f) == q * t * t * (3 * q + 2 * delta)
        ratios.append(bound / _mass(f))
        assert ratios[-1] == t * t / (128 * (3 * q + 2 * delta)) > 1
        assert t / q == 2 + Fraction(1, q * (2 * q + 1))
    assert ratios == sorted(ratios) and ratios[-1] > 10**4
    assert 97 * (2 * 97 + 1) == 18915  # the separation 2 + 1/18915 at q = 97
    q = 97
    g = _rows_need_n(2, q, 82)
    assert _mass(g) >= Fraction(q, 2) * Fraction(82 * q, 2) ** 4 / 4


def _e_upper() -> Fraction:
    """A rational upper bound for ``e``: the series to ``1/15!`` plus a tail
    below ``2/16!``."""
    terms, term = Fraction(0), Fraction(1)
    for k in range(16):
        terms += term
        term /= k + 1
    return terms + 2 * term


def test_full_count_threshold() -> None:
    """The last clause of ``lem:tropcount``: with ``kappa = n`` the criterion
    holds exactly below ``theta_n``; ``rho_1 = 2``, ``rho_2 = 4``,
    ``rho_n < 7n/3`` (from ``e^3 < (11/7)^7``), and ``3 rho_n < 81`` exactly
    for ``n <= 13``, as ``cor:fewabove`` uses.  On random multiples every
    central index at ``r`` just inside ``T/rho_n`` has ``n`` positions above.

    Control: ``rho_1 = 2`` cannot be lowered.  Every coefficient of
    ``x^10 - sum_(i<10) x^i`` has modulus 1, so ``10`` is a central index at
    ``r = 1``, with no position above it, while a zero lies above
    ``2 - 2^-9``."""
    eps = Fraction(1, 1000)
    assert _count_criterion(1, 1, Fraction(1, 2) - eps)
    assert not _count_criterion(1, 1, Fraction(1, 2))
    assert _count_criterion(2, 2, Fraction(1, 4) - eps)
    assert not _count_criterion(2, 2, Fraction(1, 4))
    assert _e_upper() ** 3 < Fraction(11, 7) ** 7
    for n in range(1, 151):
        assert _count_criterion(n, n, Fraction(3, 7 * n))
    assert all(_count_criterion(n, n, Fraction(1, 27)) for n in range(1, 14))
    assert not _count_criterion(14, 14, Fraction(1, 27))
    rng = random.Random(SEED + 17)
    for _ in range(100):
        pair = rng.choice(PYTHAGOREAN[:5])
        t = rng.randint(4, 40)
        for factor, n, big_t in ((_pair(*pair[:2]), 2, pair[2]), ([t, 1], 1, t)):
            f = _mul(factor, _cofactor(rng))
            rho_n = 4 if n == 2 else 2
            r = Fraction(big_t, rho_n) - Fraction(1, 100)
            assert _count_criterion(n, n, r / big_t)
            assert all(len(f) - 1 - y >= n for y in _central(f, r))
    big_d = 10
    f = [-1] * big_d + [1]
    assert big_d in _central(f, Fraction(1))

    def value(x: Fraction) -> Fraction:
        return sum(c * x**i for i, c in enumerate(f))

    assert value(2 - Fraction(1, 2 ** (big_d - 1))) < 0 < value(Fraction(2))


def _few_above_positions(f: Poly, moduli: list[list[int]], kinds: list[str]) -> None:
    """The positions of the proof of ``cor:fewabove``: a central index at ``1``,
    and for each gap either one central index at ``r_a = 3 U_(a-1) + 1`` with
    ``T_a > rho_(n_a) r_a`` (``"one"``), counted and charged in full, or the
    two positions of ``thm:fixedgap`` (``"two"``), charged together."""
    big_d, lead = len(f) - 1, abs(f[-1])
    charge = [
        Fraction(lead, 2) * prod(Fraction(rho, 2) for m in moduli[a:] for rho in m)
        for a in range(len(moduli))
    ]
    y1 = max(_central(f, Fraction(1)))
    positions = [y1]
    assert abs(f[y1]) > charge[0]
    for a in range(1, len(moduli)):
        n_a = sum(map(len, moduli[a:]))
        low, up = min(moduli[a]), max(moduli[a - 1])
        if kinds[a] == "one":
            r = Fraction(3 * up + 1)
            assert _count_criterion(n_a, n_a, r / low)
            ys = _central(f, r)
            assert min(ys) > positions[-1]
            for y in ys:
                assert big_d - y >= n_a and abs(f[y]) > charge[a]
            positions.append(max(ys))
            continue
        assert low > 81 * up
        lo, hi = Fraction(3 * up + 1), Fraction(low, 3)
        y_lo, y_hi = max(_central(f, lo)), max(_central(f, hi))
        assert min(_central(f, lo)) > positions[-1]
        ys = sorted({y_lo, y_hi})
        if len(ys) == 1:
            assert big_d - ys[0] >= n_a and abs(f[ys[0]]) > charge[a]
        else:
            assert abs(f[ys[0]] * f[ys[1]]) > charge[a] * Fraction(lead, 2) * 2**n_a
        positions += ys
    assert positions[-1] < big_d


def test_few_roots_above() -> None:
    """``cor:fewabove`` on random multiples.  Two annuli with one root above
    the gap at ``T_2`` just above ``2(3 U_1 + 1)`` (separation about 6) or a
    conjugate pair at ``T_2`` just above ``4(3 U_1 + 1)`` (about 12): one
    central index carries the charge, the rows and the mass bound hold.
    Three annuli with a pair on top at about ``12``, the middle gap either at
    ``7 n_2`` (item 1, rows included) or at ``81`` (item 2).

    Control: ``T_2 > 4 r`` is needed for the full count.  In
    ``prop:gaptwo`` at ``q = 97``, the central index at ``r = 3q/2``, where
    ``T_2/r < 4/3``, has one position above it, not two; and with one root
    above the gap the bound fails at the separation ``103/100``:
    ``(x - 100)(x + 103)``."""
    rng = random.Random(SEED + 18)
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    for _ in range(60):
        lower = [rng.choice(small) for _ in range(rng.randint(1, 2))]
        up = max(p[2] for p in lower)
        factors = [_pair(x, y) for x, y, _ in lower]
        moduli = [[rho for *_, rho in lower for _ in range(2)]]
        if rng.random() < 0.5:
            t = 2 * (3 * up + 1) + rng.randint(1, 3)
            factors.append([rng.choice([-1, 1]) * t, 1])
            moduli.append([t])
        else:
            x, y, rho = rng.choice(small)
            c = 4 * (3 * up + 1) // rho + 1
            factors.append(_pair(c * x, c * y))
            moduli.append([c * rho] * 2)
        f = _mul(_product(factors), _cofactor(rng))
        _few_above_positions(f, moduli, ["", "one"])
        b = _b(f)
        charge = Fraction(abs(f[-1]), 2) * prod(Fraction(rho, 2) for rho in moduli[1])
        assert b[1] > charge
        assert _mass(f) >= _fixed_gap_bound(f, moduli)
    kinds = set()
    for _ in range(40):
        lower = [rng.choice(small) for _ in range(rng.randint(1, 2))]
        middle = [rng.choice(small) for _ in range(rng.randint(1, 3))]
        x, y, rho = rng.choice(small)
        kind = rng.choice(["one", "two"])
        kinds.add(kind)
        n_2 = 2 * len(middle) + 2
        up = max(p[2] for p in lower)
        need = 81 * up + 30 if kind == "two" else 7 * n_2 * (3 * up + 1) // 3 + 1
        c = need // min(p[2] for p in middle) + 1
        middle = [(c * a, c * b, c * r) for a, b, r in middle]
        up = max(p[2] for p in middle)
        c = 4 * (3 * up + 1) // rho + 1
        top = (c * x, c * y, c * rho)
        f = _mul(
            _product([_pair(a, b) for a, b, _ in lower + middle + [top]]),
            _cofactor(rng),
        )
        moduli = [
            [p[2] for p in ann for _ in range(2)] for ann in (lower, middle, [top])
        ]
        _few_above_positions(f, moduli, ["", kind, "one"])
        assert _mass(f) >= _fixed_gap_bound(f, moduli)
        if kind == "one":
            b, lead = _b(f), abs(f[-1])
            for k in range(1, 4):
                charge = Fraction(lead, 2) * prod(
                    Fraction(rho, 2) for m in moduli[k - 1 :] for rho in m
                )
                assert b[k - 1] > charge
    assert kinds == {"one", "two"}
    q = 97
    delta = Fraction(1, 2 * q + 1)
    t = 2 * q + delta
    f = _mul([Fraction(-q), Fraction(1)], _mul([t, Fraction(1)], [t, Fraction(1)]))
    r = Fraction(3 * q, 2)
    assert t / r < Fraction(4, 3) + Fraction(1, 1000)
    assert [len(f) - 1 - y for y in _central(f, r)] == [1]
    g = _mul([-100, 1], [103, 1])
    assert _mass(g) == 3 * 100 * 103 < Fraction(100 * 103 * 103, 32)


# A second position below the gap, two annuli (lem:twobelow, cor:twofixed).


def _gamma(n: int, a: Fraction, big_t: Fraction) -> Fraction:
    """``Gamma`` of ``lem:twobelow``."""
    lam = 1 - n * a / big_t
    assert a > 1 and lam > 0
    return (1 - a / big_t) ** -n * a / ((a - 1) * lam) + (1 - 1 / big_t) ** -n


def _two_below(f: Poly, n: int, bound: Fraction) -> None:
    """For every position ``j`` some ``l <= D - n``, ``l != j``, reaches the
    bound."""
    d = len(f) - 1 - n
    for j in range(len(f)):
        assert max(abs(f[i]) for i in range(d + 1) if i != j) >= bound


def _power_family(big_k: int, q: int, lam: Fraction) -> tuple[list[Fraction], Fraction]:
    """``(x - q)(x + t)^K`` with ``t = Kq/(1 - lam)``, so ``f_1 = lam t^K``."""
    t = big_k * q / (1 - lam)
    one = Fraction(1)
    return _mul([Fraction(-q), one], _product([[t, one]] * big_k)), t


def test_second_position_below_the_gap() -> None:
    """``lem:twobelow`` on the seeded multiples of ``thm:rowstwo``: for every
    ``j`` a position ``l <= D - n``, ``l != j``, has ``|f_l| >= |f_D| Pi /
    Gamma``, and for ``n >= 2``, ``b_2 >= (lambda/8)(1 - 1/a) |f_D| Pi``; on
    ``(x - q)(x + t)^K`` with ``t = Kq/(1 - lambda)`` the ratio ``b_2 / Pi``
    is ``lambda``, linear as the lemma says, far above ``lambda^2``.

    Control: without the factor ``lambda`` in ``Gamma`` the bound fails, at
    ``lambda = 1/1000``."""
    rng = random.Random(SEED + 34)
    for _ in range(300):
        alpha = rng.choice([-1, 1]) * rng.randint(2, 12)
        factors, moduli = [], []
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.5:
                x, y, rho = rng.choice(PYTHAGOREAN[:5])
                factors.append(_pair(x, y))
                moduli += [rho, rho]
            else:
                t = rng.randint(1, 40)
                factors.append([-rng.choice([-1, 1]) * t, 1])
                moduli.append(t)
        n = len(moduli)
        scale = n * abs(alpha) // min(moduli) + rng.randint(1, 3)
        factors = [
            [c * scale ** (len(p) - 1 - i) for i, c in enumerate(p)] for p in factors
        ]
        moduli = [scale * m for m in moduli]
        f = _product([[-alpha, 1], _cofactor(rng), *factors])
        a, big_t = Fraction(abs(alpha)), Fraction(min(moduli))
        pi = abs(f[-1]) * prod(moduli)
        _two_below(f, n, pi / _gamma(n, a, big_t))
        if n >= 2:
            lam = 1 - n * a / big_t
            assert _b(f)[1] >= lam / 8 * (1 - 1 / a) * pi
    for big_k, lam in product((2, 3, 10), (Fraction(1, 2), Fraction(1, 1000))):
        q = 4 ** (big_k + 6)
        f, t = _power_family(big_k, q, lam)
        pi = t**big_k
        assert f[1] == lam * pi == _b(f)[1]
        _two_below(f, big_k, pi / _gamma(big_k, Fraction(q), t))
        assert _b(f)[1] >= lam / 8 * (1 - Fraction(1, q)) * pi
        assert _b(f)[1] > 100 * lam**2 / 2 * pi or lam == Fraction(1, 2)
    big_k, lam, q = 2, Fraction(1, 1000), 4**8
    f, t = _power_family(big_k, q, lam)
    a = Fraction(q)
    no_lam = (1 - a / t) ** -big_k * a / (a - 1) + (1 - 1 / t) ** -big_k
    assert _b(f)[1] < t**big_k / no_lam


def _gamma_bound(n: int, g: Fraction) -> Fraction:
    """``gamma_n`` of the proof of ``cor:twofixed``."""
    return Fraction(3, 2) * (1 - 1 / g) ** -n * g / (g - n) + (1 - 1 / (3 * g)) ** -n


def _separation(n: int) -> Fraction:
    """``g`` of ``cor:twofixed``."""
    return Fraction(4) if n <= 3 else n * (1 + Fraction(3, 2**n))


def test_two_annuli_at_a_fixed_separation() -> None:
    """``cor:twofixed``: ``gamma_n <= 2^(n+1)`` at ``g = 4`` for ``n <= 3`` and
    at ``g = n(1 + 3 * 2^-n)`` above, exactly for ``n <= 150``, with the
    constants of the proof; ``g <= max(4, n + 1)``.  On seeded multiples with
    a pair below and ``n_2`` real zeros or pairs at ``T_2`` just above
    ``g U_1``, and on ``(x - q)(x + t)^K`` with ``t`` just above ``g q``, the
    rows ``k = 1, 2`` and the mass bound hold.

    Control: item 2, ``(x - q)(x + t)^K`` at ``t = Kq/(1 - 2^(-K-1))``, misses
    the row ``k = 2``, while ``t = Kq/(1 - 2^-K)`` meets it; and at
    ``t = Kq/(1 - 2^(-2K-4))``, ``b_1 b_2`` misses the mass bound, which
    the positions ``2, ..., K`` restore for ``K >= 2`` (for ``K = 1`` there
    are none, and the separation ``64/63`` is below ``32/31``)."""
    for n in range(1, 151):
        g = _separation(n)
        assert g <= max(4, n + 1) and g > n
        assert _gamma_bound(n, g) <= 2 ** (n + 1)
        if n >= 4:
            assert g / (g - n) == 1 + Fraction(2**n, 3)
            assert (1 - Fraction(1, n)) ** -n <= Fraction(4, 3) ** 4 < Fraction(19, 6)
            assert (1 - Fraction(1, 3 * n)) ** -n <= Fraction(12, 11) ** 4
            assert _gamma_bound(n, g) < Fraction(19, 12) * 2**n + Fraction(37, 6)
    assert Fraction(12, 11) ** 4 < Fraction(17, 12)
    assert Fraction(19, 4) + Fraction(17, 12) == Fraction(37, 6)
    rng = random.Random(SEED + 35)
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    for _ in range(80):
        x0, y0, low_rho = rng.choice(small)
        upper: list[tuple[Poly, int]] = []
        for _ in range(rng.randint(1, 5)):
            x, y, rho = rng.choice(small)
            upper.append((_pair(x, y), rho) if rng.random() < 0.5 else ([rho, 1], rho))
        n_2 = sum(len(p) - 1 for p, _ in upper)
        g = _separation(n_2)
        scale = int(g * low_rho) // min(rho for _, rho in upper) + 1
        upper = [
            ([c * scale ** (len(p) - 1 - i) for i, c in enumerate(p)], scale * rho)
            for p, rho in upper
        ]
        assert min(rho for _, rho in upper) > g * low_rho
        f = _mul(_product([_pair(x0, y0)] + [p for p, _ in upper]), _cofactor(rng))
        lead = abs(f[-1])
        up = [rho for p, rho in upper for _ in range(len(p) - 1)]
        b1 = Fraction(lead, 2) * prod(Fraction(r, 2) for r in [low_rho] * 2 + up)
        b2 = Fraction(lead, 2) * prod(Fraction(r, 2) for r in up)
        b = _b(f)
        assert b[0] > b1 and b[1] > b2
        assert _mass(f) >= lead * b1 * b2
    for big_k, q in product(range(1, 9), (4, 5, 4**8)):
        t = int(_separation(big_k) * q) + 1
        f = _mul([-q, 1], _product([[t, 1]] * big_k))
        b2 = Fraction(1, 2) * Fraction(t, 2) ** big_k
        b1 = Fraction(1, 2) * Fraction(q, 2) * Fraction(t, 2) ** big_k
        assert _b(f)[1] > b2 and _mass(f) >= b1 * b2
    for big_k in range(1, 7):
        q = 4 ** (big_k + 1)
        f, t = _power_family(big_k, q, Fraction(1, 2 ** (big_k + 1)))
        assert t / q == big_k / (1 - Fraction(1, 2 ** (big_k + 1)))
        assert _b(f)[1] <= Fraction(1, 2) * (t / 2) ** big_k
        f, t = _power_family(big_k, q, Fraction(1, 2**big_k))
        assert _b(f)[1] > Fraction(1, 2) * (t / 2) ** big_k
        q = 2 ** (3 * big_k + 5)
        f, t = _power_family(big_k, q, Fraction(1, 2 ** (2 * big_k + 4)))
        b = _b(f)
        bound = Fraction(q, 2) * (t / 2) ** (2 * big_k) / 4  # exp of the mass bound
        assert b[0] == q * t**big_k and b[0] * b[1] * 2 <= bound
        assert (bound <= _mass(f)) == (big_k >= 2)


# One or two roots above the gap (lem:twozeros, cor:twonear).


def _zero_factor(rng: random.Random, above: Fraction) -> tuple[Poly, int]:
    """A real zero of either sign or a Pythagorean pair, of integer modulus
    just above ``above``; returns the factor and the modulus."""
    x, y, rho = rng.choice([p for p in PYTHAGOREAN if p[2] >= 5])
    if rng.random() < 0.5:
        k = int(above / rho) + 1
        return _pair(k * x, k * y), k * rho
    t = int(above) + 1
    return [-rng.choice([-1, 1]) * t, 1], t


def _two_zeros_sides(f: Poly, a: int, b: int, j: int) -> tuple[Fraction, Fraction]:
    """The two sides of ``lem:twozeros``."""
    big_d, rho = len(f) - 1, Fraction(a, b)
    left = abs(f[-1]) * b * (1 - rho ** (big_d - j))
    right = sum(
        abs(f[i]) * (1 + rho ** (i - j)) * Fraction(b) ** (i - big_d + 1)
        for i in range(j + 1, big_d)
    ) + sum(
        abs(f[i])
        * (Fraction(a) ** (i - j) + Fraction(b) ** (i - j))
        * Fraction(b) ** (j - big_d + 1)
        for i in range(j)
    )
    return left, right


def test_two_zeros_one_excluded_position() -> None:
    """``lem:twozeros`` at every position ``j`` of seeded multiples of a zero
    of modulus ``a`` and one of modulus ``b > a`` (real of both signs or
    Pythagorean pairs), with its two consequences; equality at
    ``(x - q)(x + q + 1)`` and ``j = 0``.

    Control: without the factor ``1 - rho^(D - j)`` the inequality fails
    there."""
    rng = random.Random(SEED + 46)
    for _ in range(300):
        low, a = _zero_factor(rng, Fraction(rng.randint(1, 20)))
        high, b = _zero_factor(rng, Fraction(a * rng.randint(11, 40), 10))
        f = _product([low, high, _cofactor(rng)])
        big_d, rho, lead = len(f) - 1, Fraction(a, b), abs(f[-1])
        assert 1 < a < b
        for j in range(big_d):
            left, right = _two_zeros_sides(f, a, b, j)
            assert left <= right
            if j == big_d - 1:
                weight = Fraction(1, a - 1) + Fraction(1, b - 1)
                assert max(abs(c) for c in f[: big_d - 1]) * weight >= lead * b * (
                    1 - rho
                )
            else:
                m = max((abs(f[i]) for i in range(big_d - 1) if i != j), default=0)
                weight = (1 + rho) / (b - 1) + Fraction(1, b * (a - 1))
                assert lead * b * (1 - rho**2) <= (1 + rho) * abs(f[-2]) + weight * m
    for q in (2, 5, 97):
        f = _mul([-q, 1], [q + 1, 1])
        left, right = _two_zeros_sides(f, q, q + 1, 0)
        assert left == right and abs(f[-1]) * (q + 1) > right


def test_two_annuli_near_the_least_separation() -> None:
    """``cor:twonear``, with the constants of its proof exactly.  Item 1 on
    seeded multiples with a zero or pair of modulus ``a`` below and one zero
    (possibly of a pair) at ``T_2`` just above ``(4/3 + 2/(3a)) a``, and on
    ``(x - q)(x + t)``: the second row; item 2 likewise with two zeros above
    ``(2 + 1/a) a``, and on ``(x - q)(x + t)^2``: the mass bound, a
    largest nonleading coefficient at most at ``D - 2``, the positions of
    the proof, and the second position of ``prop:rowstwolarge`` excluding
    every position in turn.

    Control: ``(x - q)(x + t)`` just below ``t = 4q/3`` misses the row, also
    at ``q = 3 * 10^6``, so ``4/3`` cannot be lowered; and
    ``prop:gaptwo`` misses the mass at ``T_2 = (2 + 1/(q(2q + 1))) U_1``,
    below ``2 + 1/q``."""
    # Item 1: the identity behind the case j <= D - 2, and its sign.
    for tau in (
        Fraction(3),
        Fraction(31, 10),
        Fraction(4),
        Fraction(97),
        Fraction(10**6),
    ):
        g = Fraction(4, 3) + Fraction(2, 3 * tau)
        assert 3 - 4 / g == 3 / (2 * tau + 1) and g * tau - 1 == (4 * tau - 1) / 3
        diff = 3 / (2 * tau + 1) - 3 / (4 * tau - 1) - 3 / ((4 * tau + 2) * (tau - 1))
        assert diff == 3 * (2 * tau - 1) * (2 * tau - 5) / (
            2 * (2 * tau + 1) * (4 * tau - 1) * (tau - 1)
        )
        assert diff > 0 and g * tau > 4 and 4 * (1 - 1 / g) >= 1
    # Item 2: the numbers for g = 2 + 1/tau.
    for tau in (
        Fraction(3),
        Fraction(31, 10),
        Fraction(4),
        Fraction(97),
        Fraction(10**6),
    ):
        g = 2 + 1 / tau
        bt = g * tau
        assert bt == 2 * tau + 1 and 1 - 2 / g == 1 / (2 * tau + 1)
        assert 1 - 1 / g == (tau + 1) / (2 * tau + 1)
        assert g * g * tau**3 == tau * (2 * tau + 1) ** 2 >= 147
        assert bt / (bt - 1) <= Fraction(7, 6) and bt / (tau - 1) <= Fraction(7, 2)
        eps = Fraction(24, 49) / (2 * tau + 1)
        assert eps == (1 - 2 / g) * Fraction(2, 3) / Fraction(7, 6) ** 2
        kappa = 1 - 1 / g - (bt / (bt - 1) + 1 / (tau - 1)) / 8
        assert bt * kappa >= (34 * tau + 20) / 48 > 1 / (8 * eps)
        assert 4 * (34 * tau + 20) - 49 * (2 * tau + 1) == 38 * tau + 31
    rng = random.Random(SEED + 47)
    for _ in range(150):
        low, a = _zero_factor(rng, Fraction(rng.randint(3, 30)))
        g1 = Fraction(4, 3) + Fraction(2, 3 * a)
        high, b = _zero_factor(rng, g1 * a)
        f = _product([low, high, _cofactor(rng)])
        lead, bs = abs(f[-1]), _b(f)
        assert 4 * bs[1] > lead * b
        assert 2 * bs[0] > lead * prod(
            Fraction(r, 2) for r in [a] * (len(low) - 1) + [b]
        )
        g2 = 2 + Fraction(1, a)
        highs = [_zero_factor(rng, g2 * a)]
        if len(highs[0][0]) == 2:
            highs.append(_zero_factor(rng, g2 * a * rng.choice([1, 2])))
            highs = [(p, r) for p, r in highs if len(p) == 2][:2]
            if len(highs) < 2:
                highs.append(([highs[0][1], 1], highs[0][1]))
        f = _product([low, *(p for p, _ in highs), _cofactor(rng)])
        up = [r for p, r in highs for _ in range(len(p) - 1)]
        assert len(up) == 2 and min(up) > g2 * a
        lead, big_d = abs(f[-1]), len(f) - 1
        low_moduli = [a] * (len(low) - 1)
        bound = (
            lead**3
            * prod(Fraction(r, 2) for r in low_moduli)
            * prod(Fraction(r, 2) ** 2 for r in up)
            / 4
        )
        assert _mass(f) >= bound
        j = _central(f, Fraction(1))[0]
        assert j <= big_d - 2
        m = max(abs(f[i]) for i in range(big_d - 1) if i != j)
        pi8 = Fraction(lead * prod(up), 8)
        assert m >= pi8 or abs(f[-2]) * m >= pi8
        # The second position of prop:rowstwolarge, excluding any position.
        big_t, gp = min(up), (1 - Fraction(1, min(up))) ** -2
        lam = 1 - Fraction(2 * a, big_t)
        eps = min(
            lam * (a - 1) / (gp * (a - lam)), (a - 1) / (1 + (2 * a - 1) * (gp - 1))
        )
        assert eps >= Fraction(24, 49) / (2 * a + 1)
        for j in range(big_d + 1):
            others = [abs(f[i]) for i in range(big_d - 1) if i != j]
            assert max(others) >= eps * lead * prod(up)
    for q in (4, 5, 97, 10**4):
        t = 2 * q + 2
        f = _mul([-q, 1], _mul([t, 1], [t, 1]))
        assert _mass(f) >= Fraction(q, 2) * Fraction(t, 2) ** 4 / 4
        assert _central(f, Fraction(1)) == [0] and 8 * abs(f[1]) * f[2] >= t * t
        t = int((Fraction(4, 3) + Fraction(2, 3 * q)) * q) + 1
        assert 4 * _b(_mul([-q, 1], [t, 1]))[1] > t
    for k in (2, 5, 10**6):
        q, t = 3 * k, 4 * k - 1
        assert 4 * _b(_mul([-q, 1], [t, 1]))[1] < t
    for q in (97, 1000):
        t = 2 * q + Fraction(1, 2 * q + 1)
        assert 2 < t / q < 2 + Fraction(1, q)
        f = _mul([Fraction(-q), Fraction(1)], _mul([t, Fraction(1)], [t, Fraction(1)]))
        assert _mass(f) < Fraction(q, 2) * (t / 2) ** 4 / 4


# Real roots of both signs (cor:bothsignsmass, prop:bothsignssharp).


def _both_signs_row(big_l: int, big_r: int, k: int) -> Fraction:
    return Fraction(Fraction(big_r, 2) ** (big_l - 2 * k + 2) - 1, 2**k - 1)


def _both_signs_mass(big_l: int, big_r: int) -> Fraction:
    """``exp`` of the right side of ``eq:bothmass`` at ``|f_D| = 1``."""
    half = -(-big_l // 2)
    return Fraction(big_r, 2) ** ((big_l + 1) ** 2 // 4) / 2 ** (half * (half + 3) // 2)


@pytest.mark.parametrize("big_r", [4, 5, 6])
def test_both_signs(big_r: int) -> None:
    rng = random.Random(SEED + big_r)
    for _ in range(150):
        roots = [
            rng.choice([-1, 1]) * rng.randint(big_r, big_r + 3)
            for _ in range(rng.randint(1, 5))
        ]
        big_l = len(roots)
        f = _mul(_product([[-z, 1] for z in roots]), _cofactor(rng))
        b = _b(f)
        for k in range(1, -(-big_l // 2) + 1):
            assert b[k - 1] >= abs(f[-1]) * _both_signs_row(big_l, big_r, k)
        half = -(-big_l // 2)
        assert _mass(f) >= abs(f[-1]) ** (half + 1) * _both_signs_mass(big_l, big_r)


def test_both_signs_sharp() -> None:
    """``prop:bothsignssharp`` at ``prod (x^2 - s_j^2)``, ``s_j in [R, lambda R]``.

    Control: the one-sign mass ``L(L+1)/2 log(R-1)`` of
    ``cor:mass`` fails there, so the mixed problem really is weaker.
    """
    rng = random.Random(SEED + 3)
    for _ in range(100):
        big_r, lam = rng.randint(4, 8), rng.randint(1, 3)
        s = [rng.randint(big_r, lam * big_r) for _ in range(rng.randint(1, 5))]
        big_l = 2 * len(s)
        p = _product([[-x * x, 0, 1] for x in s])
        assert _mass(p) <= (lam * big_r) ** ((big_l + 1) ** 2 // 4) * 2 ** len(s) ** 2
    p = _product([[-(100**2), 0, 1]] * 4)
    assert _mass(p) < 99 ** (8 * 9 // 2)


def test_counting_identities() -> None:
    """The two sums the proofs of the mass corollary and its sharpness use."""
    for big_l in range(1, 40):
        half = -(-big_l // 2)
        assert sum(big_l - 2 * k + 2 for k in range(1, half + 1)) == (
            (big_l + 1) ** 2 // 4
        )
        assert 2 * sum(k + 1 for k in range(1, half + 1)) == half * (half + 3)
    for m in range(1, 40):
        assert m * (m + 1) == (2 * m + 1) ** 2 // 4


# The transfer as an equality of infima (thm:transfer, cor:imag item 3).


@pytest.mark.parametrize(("squares", "k"), [((2,), 1), ((2, 3), 1), ((2, 3), 2)])
def test_imaginary_infimum_is_the_real_one(squares: tuple[int, ...], k: int) -> None:
    """``min b_k`` over multiples of ``P_im`` of degree ``<= 2 cap + 1`` is
    ``min b_k`` over multiples of ``P_re`` of degree ``<= cap``, exactly.

    The common value obeys the row of ``cor:imag`` and, as the control, breaks
    the same row with ``c_j^2`` in place of ``c_j^2 - 1``.
    """
    cap = 5
    p_re = [Fraction(c) for c in _product([[-c2, 1] for c2 in squares])]
    p_im = [Fraction(c) for c in _product([[c2, 0, 1] for c2 in squares])]
    real = min_bk_of(p_re, k, cap)
    assert min_bk_of(p_im, k, 2 * cap + 1) == real
    assert real >= prod(c2 - 1 for c2 in squares[k - 1 :])
    assert real < prod(squares[k - 1 :])


@pytest.mark.parametrize(("a", "b", "rho"), [(3, 4, 5), (5, 12, 13), (0, 2, 2)])
def test_first_row_at_the_optimum(a: int, b: int, rho: int) -> None:
    """``prop:rowone`` at the exact ``min b_1`` over multiples of degree ``<= 9``
    of ``(x - a - bi)(x - a + bi)``; control: ``rho^2`` in place of
    ``(rho - 1)^2`` fails there."""
    best = min_bk_of([Fraction(rho * rho), Fraction(-2 * a), Fraction(1)], 1, 9)
    assert (rho - 1) ** 2 <= best < rho**2


# Blocks at Gaussian roots (lem:gausscarry, lem:gaussblocks, thm:gausscharge).

Gauss = tuple[int, int]  # a + bi


def _gmul(z: Gauss, w: Gauss) -> Gauss:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def _pairs(roots: list[Gauss]) -> Poly:
    return _product([[a * a + b * b, -2 * a, 1] for a, b in roots])


#: Primitive Gaussian integers of pairwise coprime odd norms 5, 13, 17, 29.
COPRIME = [(1, 2), (-2, 3), (4, 1), (-5, 2)]


def _tail(f: Poly, m: int, z: Gauss) -> Gauss:
    """``G_m(z) = sum_(i >= m) f_i z^(i - m)``, exactly in ``Z[i]``."""
    v = (0, 0)
    for c in reversed(f[m:]):
        v = _gmul(v, z)
        v = (v[0] + c, v[1])
    return v


def _trim(f: Poly) -> Poly:
    while f and f[-1] == 0:
        f = f[:-1]
    return f


def _blocks(f: Poly, roots: list[Gauss], shift: int = 0) -> list[tuple[int, Poly]]:
    """The decomposition of ``lem:gaussblocks``: ``f = sum x^e B``."""
    f = _trim(f)
    e = next(i for i, c in enumerate(f) if c)
    f0 = f[e:]
    for m in range(1, len(f0)):
        if all(_tail(f0, m, z) == (0, 0) for z in roots):
            return _blocks(f0[:m], roots, shift + e) + _blocks(
                f0[m:], roots, shift + e + m
            )
    return [(shift + e, f0)]


def _block_multiples(rng: random.Random, p: Poly) -> Poly:
    """A random multiple of ``p``, sometimes a lacunary sum of several."""
    f = _mul(p, _cofactor(rng))
    for _ in range(rng.randint(0, 2)):
        g = _mul(p, _cofactor(rng))
        f = f + [0] * rng.randint(0, 3) + g
    return f


def test_gaussian_blocks() -> None:
    """``lem:gaussblocks``: the blocks tile ``f`` and are multiples of ``P``
    without a clean split; every split of a block is charged as in
    ``lem:gausscarry``, and each block pays ``thm:gausscharge``.  The
    heavy coefficients of ``prop:gaussheavy`` are checked on the same
    multiples in ``tests/test_sectors.py``."""
    rng = random.Random(SEED + 7)
    for _ in range(300):
        roots = COPRIME[: rng.randint(1, len(COPRIME))]
        norms = [a * a + b * b for a, b in roots]
        n_min = min(norms)
        p = _pairs(roots)
        f = _block_multiples(rng, p)
        blocks = _blocks(f, roots)
        tiled = [0] * len(f)
        for e, blk in blocks:
            for i, c in enumerate(blk):
                tiled[e + i] += c
            assert _divides(p, blk)
            d = len(blk) - 1
            for m in range(1, d + 1):
                bad = [
                    (z, n)
                    for z, n in zip(roots, norms, strict=True)
                    if _tail(blk, m, z) != (0, 0)
                ]
                assert bad
                z, n = bad[0]
                assert any(4 ** (m - i) * blk[i] ** 2 >= n ** (m - i) for i in range(m))
            assert 4**d * prod(max(1, c * c) for c in blk[:d]) >= n_min**d
        assert tiled == _trim(f)


def test_gaussian_carry_needs_the_half() -> None:
    """Control for ``lem:gausscarry``: with ``rho`` in place of ``rho/2`` the
    charge fails at the split ``m = 5`` of ``(2 - x)P``, ``P`` the pairs of
    ``1 + 2i`` and ``-2 + 3i``, at ``-2 + 3i``."""
    roots = [(1, 2), (-2, 3)]
    f = _mul(_pairs(roots), [2, -1])
    assert f == [130, -77, 26, -6, 0, -1]
    z, n = (-2, 3), 13
    assert _tail(f, 5, z) != (0, 0)
    assert not any(f[i] ** 2 >= n ** (5 - i) for i in range(5))
    assert any(4 ** (5 - i) * f[i] ** 2 >= n ** (5 - i) for i in range(5))


# The Archimedean Newton polygon (thm:archnewton, cor:separated).


def _tropical_roots(f: Poly) -> list[float]:
    """The tropical roots ``sigma_1 > sigma_2 > ...``: walking the upper
    concave hull of ``(i, log|f_i|)`` down from the top degree, the next
    vertex is the one reached by the steepest rise, and ``sigma`` is that
    rise per step."""
    logs = {i: log(abs(c)) for i, c in enumerate(f) if c != 0}
    v, sigmas = len(f) - 1, []
    while any(j < v for j in logs):
        sigma, j = max(((logs[j] - logs[v]) / (v - j), -j) for j in logs if j < v)
        sigmas.append(sigma)
        v = -j
    return sigmas


def _active(f: Poly, r: Fraction) -> int:
    """The position maximizing ``|f_i| r^i``, the largest one on a tie."""
    return max(range(len(f)), key=lambda i: (abs(f[i]) * r**i, i))


def _dominates(f: Poly, r: Fraction) -> bool:
    v = _active(f, r)
    return abs(f[v]) * r**v > sum(abs(c) * r**i for i, c in enumerate(f) if i != v)


def test_newton_polygon_dominance() -> None:
    """At ``r = e^u`` farther than ``log 3`` from every tropical root, the
    active term exceeds the sum of all the others, exactly (item 1).

    Control: at distance ``log(5/2)`` on both sides the term need not
    dominate, as the coefficients ``5^(n-|i-n|) 2^|i-n|`` show at ``r = 1``.
    """
    rng = random.Random(SEED)
    checked = 0
    for _ in range(400):
        f = [rng.choice([-1, 1]) * 10 ** rng.randint(0, 12) * rng.randint(1, 9)]
        f += [rng.choice([0, 1]) * rng.randint(-(10**9), 10**9) for _ in range(8)]
        f.append(rng.choice([-1, 1]) * rng.randint(1, 9))
        sigmas = _tropical_roots(f)
        for _ in range(20):
            r = Fraction(rng.randint(1, 10**6), rng.randint(1, 10**6))
            u = log(r)
            if all(abs(u - s) > log(3) + 1e-9 for s in sigmas):
                assert _dominates(f, r)
                checked += 1
    assert checked >= 500
    n = 6
    g = [5 ** (n - abs(i - n)) * 2 ** abs(i - n) for i in range(2 * n + 1)]
    sigmas = _tropical_roots(g)
    assert all(abs(abs(s) - log(Fraction(5, 2))) < 1e-9 for s in sigmas)
    assert not _dominates(g, Fraction(1))


def test_separated_moduli() -> None:
    """Real roots ``rho_1 >= 3`` with ``rho_(j+1) > 9 rho_j`` force
    ``b_k >= |f_D| prod_(i>=k) rho_i/3`` for every multiple (cor:separated,
    item 1), on seeded multiples with random cofactors.

    Control: the same bound without the factor ``1/3`` fails on some of them.
    """
    rng = random.Random(SEED)
    failures = 0
    for _ in range(300):
        size = rng.randint(1, 3)
        rhos = [rng.randint(3, 6)]
        for _ in range(size - 1):
            rhos.append(9 * rhos[-1] + rng.randint(1, 5))
        roots = [rng.choice([-1, 1]) * rho for rho in rhos]
        f = _mul(_product([[-s, 1] for s in roots]), _cofactor(rng))
        b = _b(f)
        lead = abs(f[-1])
        for k in range(1, size + 1):
            tail = prod(rhos[k - 1 :])
            assert b[k - 1] * 3 ** (size - k + 1) >= lead * tail
            failures += b[k - 1] < lead * tail
    assert failures > 0
