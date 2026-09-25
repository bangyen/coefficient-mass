"""Exact checks of ``coefficient-mass-complex.tex``.

Each bound is checked on seeded random integer multiples, where every
coefficient is exact; roots of irrational modulus are avoided by using
Pythagorean Gaussian integers.  Every group has a control that a false
variant of its statement is caught.
"""

from __future__ import annotations

import random
from fractions import Fraction
from itertools import product
from math import atan, ceil, comb, exp, gcd, isqrt, log, log1p, pi, prod

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
# thm:fixedgap, prop:annulisharp).


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


def test_count_at_a_distance() -> None:
    """``lem:tropcount``: ``n`` zeros of modulus ``>= T`` put every central
    index at ``r`` at least ``kappa`` below the top whenever the criterion
    holds, in particular ``n`` at ``r = T/(3n)`` and ``n/2`` at ``r = T/6``."""
    rng = random.Random(SEED + 12)
    for _ in range(200):
        pairs = [rng.choice(PYTHAGOREAN) for _ in range(rng.randint(1, 3))]
        f = _mul(_product([_pair(a, b) for a, b, _ in pairs]), _cofactor(rng))
        n, big_t = 2 * len(pairs), min(rho for *_, rho in pairs)
        assert _count_criterion(n, n, Fraction(1, 3 * n))
        assert _count_criterion(n, -(-n // 2), Fraction(1, 6))
        for den in (3 * n, 6, 4, 3, 2):
            r = Fraction(big_t, den)
            kappa = max(k for k in range(n + 1) if _count_criterion(n, k, r / big_t))
            if den == 3 * n:
                assert kappa == n
            if den == 6:
                assert 2 * kappa >= n
            assert all(len(f) - 1 - y >= kappa for y in _central(f, r))


def test_count_needs_distance() -> None:
    """The control: at a constant distance the full count fails, and at a
    distance ratio below ``1`` so does the half count.  ``(x - 10)^12`` has
    ``12`` zeros of modulus ``10`` but a positive central index at ``10/11``,
    fewer than ``12`` positions above it at ``10/6``, and fewer than ``6`` at
    ``20``; at ``10/36`` the count is full."""
    f = _product([[-10, 1]] * 12)
    assert all(len(f) - 1 - y < 12 for y in _central(f, Fraction(10, 11)))
    assert all(6 <= len(f) - 1 - y < 12 for y in _central(f, Fraction(10, 6)))
    assert all(len(f) - 1 - y < 6 for y in _central(f, Fraction(20)))
    assert all(len(f) - 1 - y >= 12 for y in _central(f, Fraction(10, 36)))


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
    above ``162 U_(a-1)``; the top annulus may repeat one pair many times."""
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    annuli = [[rng.choice(small) for _ in range(rng.randint(1, 2))]]
    for _ in range(rng.randint(1, 2)):
        annuli.append([rng.choice(small)] * rng.randint(1, 7))
    for a in range(1, len(annuli)):
        upper = max(p[2] for p in annuli[a - 1])
        c = (162 * upper + 60) // min(p[2] for p in annuli[a]) + 1
        annuli[a] = [(c * x, c * y, c * rho) for x, y, rho in annuli[a]]
    return annuli


def _fixed_gap_positions(f: Poly, moduli: list[list[int]]) -> bool:
    """The positions of the proof of ``thm:fixedgap``, at ``r^- = 3 U_(a-1) + 1``
    and ``r^+ = T_a/6``, ordered, counted and charged as there; returns whether
    some central index at ``T_a/6`` has fewer than ``n_a`` positions above it."""
    big_d, lead = len(f) - 1, abs(f[-1])
    big_s = len(moduli)
    for a in range(1, big_s):
        assert min(moduli[a]) > 162 * max(moduli[a - 1])
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
        hi = Fraction(min(moduli[a]), 6)
        assert hi > 9 * lo
        ys = sorted({max(_central(f, lo)), max(_central(f, hi))})
        assert ys[0] > positions[-1]
        assert all(2 * (big_d - y) >= n_a for y in ys)
        if len(ys) == 1:
            assert big_d - ys[0] >= n_a
            assert abs(f[ys[0]]) > charge[a]
        else:
            value = abs(f[ys[0]] * f[ys[1]])
            assert value > charge[a] * Fraction(lead, 2) * 3**n_a
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
    """``thm:fixedgap`` at separation ``162`` on random multiples: the
    positions of its proof are ordered and counted as there, and the mass
    bound holds.

    Control: one central index is not enough.  In some samples the central
    index at ``T_a/6`` has fewer than ``n_a`` positions above it, so
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
    ``t_a > 162 t_(a-1) + 54`` (the ``+ 54`` leaves room for the radii
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
            ts.append(162 * ts[-1] + rng.randint(55, 90))
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


# Thin sectors (lem:sectorcount, thm:thinsector).

GPoly = list[tuple[int, int]]  # Gaussian-integer coefficients, constant first


def _gpoly_mul(p: GPoly, q: GPoly) -> GPoly:
    out = [(0, 0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            c, o = _gmul(a, b), out[i + j]
            out[i + j] = (o[0] + c[0], o[1] + c[1])
    return out


def _gpoly_product(factors: list[GPoly]) -> GPoly:
    out: GPoly = [(1, 0)]
    for f in factors:
        out = _gpoly_mul(out, f)
    return out


def _sector_e(x: float) -> float:
    """``E(x)`` of ``sec:thin``."""
    return 4 * x / log(2) * (1 + log(1 + pi / (2 * x)))


def _on_ray(h: GPoly, u: Gauss, n: int, e: Gauss) -> Poly:
    """``n^d Im(e B(r u/n))`` as an integer polynomial in ``r``, for ``|u| = n``:
    ``h_theta`` of ``lem:sectorcount`` at ``e^(i psi) = u/n``, ``e^(-i theta)
    = e/|e|``, up to a positive factor."""
    d, out, power = len(h) - 1, [], (1, 0)
    for k, b in enumerate(h):
        out.append(_gmul(_gmul(e, b), power)[1] * n ** (d - k))
        power = _gmul(power, u)
    return _trim(out)


def _sturm_above(p: Poly, a: Fraction) -> int:
    """The number of distinct real zeros of ``p`` in ``(a, oo)``, by Sturm's
    theorem; ``p(a) != 0``."""
    chain = [[Fraction(c) for c in p], [Fraction(i * c) for i, c in enumerate(p)][1:]]
    while len(chain[-1]) > 1:
        rem = chain[-2][:]
        div = chain[-1]
        while len(rem) >= len(div):
            f, shift = rem[-1] / div[-1], len(rem) - len(div)
            for i, c in enumerate(div):
                rem[shift + i] -= f * c
            rem.pop()
            while rem and rem[-1] == 0:
                rem.pop()
        if not rem:
            break
        chain.append([-c for c in rem])

    def changes(values: list[Fraction]) -> int:
        signs = [v > 0 for v in values if v != 0]
        return sum(x != y for x, y in zip(signs, signs[1:], strict=False))

    at_a = [sum(c * a**i for i, c in enumerate(q)) for q in chain]
    assert at_a[0] != 0
    return changes(at_a) - changes([q[-1] for q in chain])


#: The rays ``arg z = pi/4 -+ delta'`` through ``120 + 119i`` and ``119 + 120i``,
#: of modulus ``169``; ``delta' = arctan(1/239)``.
_RAYS, _RAY_N = [(120, 119), (119, 120)], 169

#: ``e^(i theta)`` at Pythagorean angles, as ``(numerator, modulus)``.
_THETAS = [
    ((x, y), rho)
    for a, b, rho in [(1, 0, 1), (3, 4, 5), (5, 12, 13), (8, 15, 17), (20, 21, 29)]
    for x, y in [(a, b), (b, a), (-a, b), (-b, a)]
]


def _crossings(h: GPoly, below: Fraction) -> list[list[int]]:
    """For each ray, the zeros of ``h_theta`` above ``below`` at every theta of
    ``_THETAS`` and at the theta of ``thm:thinsector``'s proof."""
    out = []
    for u in _RAYS:
        # e^(-i theta) b_d e^(i d psi) = i |b_d| when b_d = 1: e = i conj(u)^d.
        top = _gmul((0, 1), _gpow((u[0], -u[1]), len(h) - 1))
        es = [(z[0], -z[1]) for z, _ in _THETAS] + [top]
        out.append([_sturm_above(_on_ray(h, u, _RAY_N, e), below) for e in es])
    return out


def _sector_multiple(rng: random.Random, big_k: int) -> tuple[GPoly, int]:
    """``prod_j (x - c_j (1 + i))`` times monic linear factors at Gaussian
    points off both rays; returns it and ``min c_j``."""
    cs = [rng.randint(8, 30) for _ in range(big_k)]
    factors = [[(-c, -c), (1, 0)] for c in cs]
    while len(factors) < big_k + rng.randint(0, 3):
        g = (rng.randint(-40, 40), rng.randint(-40, 40))
        if all(_gmul(g, (u[0], -u[1]))[1] != 0 for u in _RAYS):
            factors.append([(-g[0], -g[1]), (1, 0)])
    return _gpoly_product(factors), min(cs)


def test_sector_crossings() -> None:
    """``lem:sectorcount`` at ``phi = pi/4``, ``delta' = arctan(1/239)``: some
    ray ``psi`` has, for every tested ``theta``, at least
    ``K - d E(delta')/pi - 1`` distinct zeros of ``h_theta`` in
    ``(R/2, oo)``, counted exactly by Sturm sequences; ``K`` zeros
    ``c_j(1 + i)`` lie on the bisector, of modulus at least ``R = c sqrt 2``,
    the other zeros off both rays.  Since ``r_1 >= R/2``, counting in
    ``(7c/10, oo)``, ``7c/10 < R/2``, checks a consequence of the lemma.

    Control: without its ``-1`` the bound is false.  On some samples every
    ray has a ``theta`` with fewer than ``K - d E(delta')/pi`` zeros in
    ``(7c/10, oo)``, hence in ``(r_1, oo)`` for every admissible ``r_1``; at
    ``theta = 0`` the product of four zeros on the bisector has only
    ``K - 1 = 3`` on either ray, below ``4 - 4 E(delta')/pi = 3.78...``.
    """
    rng = random.Random(SEED + 17)
    e_delta = _sector_e(atan(Fraction(1, 239)))
    caught = 0
    for _ in range(40):
        big_k = rng.randint(1, 6)
        h, c = _sector_multiple(rng, big_k)
        bound = big_k - (len(h) - 1) * e_delta / pi - 1
        counts = _crossings(h, Fraction(7 * c, 10))
        assert any(min(row) >= bound for row in counts)
        caught += all(min(row) < bound + 1 for row in counts)
    assert caught > 0
    h = _gpoly_product([[(-c, -c), (1, 0)] for c in (10, 11, 12, 13)])
    counts = _crossings(h, Fraction(7))
    assert all(row[0] == 3 < 4 - 4 * e_delta / pi for row in counts)


def _thin_rows(h: GPoly, big_r: int, big_k: int) -> bool:
    """The rows and mass of ``thm:thinsector``, exactly, on squared moduli."""
    sq = [a * a + b * b for a, b in h]
    lead, rest = sq[-1], sorted(sq[:-1], reverse=True)
    m, q = -(-big_k // 2) - 1, Fraction(big_r, 2) - 1
    rows = all(rest[k - 1] >= lead * q ** (2 * (m - k + 1)) for k in range(1, m + 1))
    mass = prod(max(1, x) for x in sq) >= lead ** (m + 1) * q ** (m * (m + 1))
    return rows and mass


#: Directions within ``arctan(1/239) < 1/200`` of ``pi/4``, as ``(u, |u|^2)``.
_NEAR_DIAGONAL = [((1, 1), 2), ((120, 119), 169**2), ((119, 120), 169**2)]


def test_thin_sector() -> None:
    """``thm:thinsector`` at ``phi = pi/4``, ``delta = 1/200``, on Gaussian
    multiples ``prod_j (x - c_j u_j) Q``: ``K`` zeros on the three Gaussian
    directions within ``delta`` of ``phi`` (angle ``0`` or ``arctan(1/239) <
    1/239``), ``R`` the integer part of their least modulus, ``Q`` random
    with Gaussian coefficients and ``d E(2 delta) <= pi K/2``.  Rows and mass
    are checked exactly with ``m = ceil(K/2) - 1``.  ``B`` is complex, so the
    ``K`` zeros need no conjugates and ``d = K`` is allowed: the hypothesis
    needs only ``delta < 0.033``, not the ``delta < 0.0134`` of real ``B``.

    Control: the degree hypothesis cannot be dropped.  ``x^502 + 6^502`` has
    ``K = 5`` zeros within ``pi/100`` of ``i``, so ``m = 2``, but ``b_2 = 0``;
    there ``d E(pi/50) > pi K/2``.
    """
    rng = random.Random(SEED + 18)
    delta = 1 / 200
    e2 = _sector_e(2 * delta)
    for _ in range(150):
        big_k = rng.randint(1, 7)
        roots = []
        for _ in range(big_k):
            (a, b), _ = rng.choice(_NEAR_DIAGONAL)
            c = rng.randint(1, 3) if a > 1 else rng.randint(5, 40)
            roots.append((c * a, c * b))
        big_r = min(isqrt(a * a + b * b) for a, b in roots)
        assert big_r >= 6
        cofactor = [
            (rng.randint(-3, 3), rng.randint(-3, 3))
            for _ in range(rng.randint(0, 2 * big_k))
        ]
        cofactor.append(rng.choice([(1, 0), (0, 1), (2, -1), (1, 1)]))
        h = _gpoly_mul(_gpoly_product([[(-a, -b), (1, 0)] for a, b in roots]), cofactor)
        assert (len(h) - 1) * e2 <= pi * big_k / 2
        assert _thin_rows(h, big_r, big_k)
    big_m, rho = 251, 6
    phases = [Fraction(2 * j + 1, 2 * big_m) for j in range(2 * big_m)]
    big_k = sum(abs(t - Fraction(1, 2)) <= Fraction(1, 100) for t in phases)
    assert big_k == 5
    h = [(rho ** (2 * big_m), 0)] + [(0, 0)] * (2 * big_m - 1) + [(1, 0)]
    assert 2 * big_m * _sector_e(pi / 50) > pi * big_k / 2
    assert not _thin_rows(h, rho, big_k)


# Wide sectors (thm:widesector, cor:wideconst, prop:widesharp).


def _in_arc(n: int, phi: Fraction, delta: Fraction) -> int:
    """Zeros of ``x^n - rho^n`` with ``|arg - phi| <= delta``, angles over ``pi``."""
    return sum(
        min((Fraction(2 * j, n) - phi) % 2, (phi - Fraction(2 * j, n)) % 2) <= delta
        for j in range(n)
    )


_PHIS = [Fraction(i, 37) for i in range(74)]


@pytest.mark.parametrize("delta", [Fraction(1, 7), Fraction(1, 3), Fraction(3, 4), 1])
def test_roots_of_unity_fill_a_sector(delta: Fraction) -> None:
    """``x^N - rho^N``, ``N = ceil(pi K/delta)``, has ``K`` zeros in the arc."""
    for big_k in range(1, 12):
        n = ceil(big_k / delta)
        assert all(_in_arc(n, phi, delta) >= big_k for phi in _PHIS)


def test_roots_of_unity_control() -> None:
    """One degree fewer does not always reach ``K``: the ceiling is needed."""
    delta, big_k = Fraction(1, 3), 5
    n = ceil(big_k / delta) - 1
    assert any(_in_arc(n, phi, delta) < big_k for phi in _PHIS)


def _kappa_upper(delta: float) -> float:
    """An upper bound for ``kappa(delta)`` of ``sec:widesectors``.  A larger
    ``kappa`` only lowers the bounds of ``thm:widesector`` and
    ``cor:wideconst``, so they hold with it, and a variant that fails with it
    fails with ``kappa`` itself."""
    return min(log(2), 2 * delta / pi * (1 + log(pi / (2 * delta))))


def _log_minus_one(u: float) -> float:
    """``log(e^u - 1)`` for ``u > 0`` without overflow."""
    return u + log1p(-exp(-u))


def _wide_bound(
    big_k: int, d: int, delta: float, log_r: float, log_t: float, m: int, rate: float
) -> float:
    """The right side of ``thm:widesector`` with ``pi/delta`` replaced by
    ``rate``; the theorem has ``rate = pi/delta``."""
    omega = _kappa_upper(delta) * d / log_t
    nu = rate * max(0.0, big_k - 1 - m - omega)
    g = nu * (log_r - log_t) - log(nu + 1) - 1
    return min(m * (m + 1) / 2 * _log_minus_one(log_r - log_t), g)


def _wide_const_bound(
    big_k: int, delta: float, lam: float, eps: float, log_r: float, rate: float
) -> float:
    """The right side of ``cor:wideconst``, ``T = exp(kappa lambda/eps)``,
    with ``pi/delta`` replaced by ``rate``."""
    log_t = _kappa_upper(delta) * lam / eps
    assert log_r >= log(3) + log_t
    return min(
        eps**2 * big_k**2 / 2 * _log_minus_one(log_r - log_t),
        rate * ((1 - 2 * eps) * big_k - 2) * (log_r - log_t)
        - log(pi * big_k / delta + 1)
        - 1,
    )


def test_wide_sector() -> None:
    """``thm:widesector`` at ``phi = delta = pi/4`` (the closed first
    quadrant), ``T = 10``, ``R = 30``, for every ``m <= K + 1``, on Gaussian
    multiples ``prod_j (x - beta_j) Q``: ``K`` zeros ``a + bi``, ``a, b >= 0``,
    of modulus at least ``R`` (exactly: ``a^2 + b^2 >= 900``), ``Q`` random
    with Gaussian coefficients.  The masses are exact; the logarithms are
    floating point, with ``kappa`` replaced by an upper bound.  The control
    is in ``test_wide_sector_constant``.
    """
    rng = random.Random(SEED + 19)
    delta, log_t, log_r = pi / 4, log(10), log(30)
    for _ in range(150):
        big_k = rng.randint(1, 8)
        roots: list[Gauss] = []
        while len(roots) < big_k:
            z = (rng.randint(0, 60), rng.randint(0, 60))
            if z[0] ** 2 + z[1] ** 2 >= 900:
                roots.append(z)
        cofactor = [
            (rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(rng.randint(0, 3))
        ]
        cofactor.append(rng.choice([(1, 0), (0, 1), (2, -1), (1, 1)]))
        h = _gpoly_mul(_gpoly_product([[(-a, -b), (1, 0)] for a, b in roots]), cofactor)
        mass = sum(log(max(1, a * a + b * b)) for a, b in h) / 2
        for m in range(big_k + 2):
            bound = _wide_bound(big_k, len(h) - 1, delta, log_r, log_t, m, pi / delta)
            assert mass >= bound - 1e-9


def test_wide_sector_constant() -> None:
    """``thm:widesector`` and ``cor:wideconst`` at ``x^N - rho^N``,
    ``N = ceil(pi K/delta)`` (``prop:widesharp``), ``delta = pi/4``,
    ``K = 10^4``, ``log rho = 1000``: its ``K`` zeros in the closed first
    quadrant are counted exactly, ``Lambda = N log rho``, and the bounds hold,
    at ``lambda = pi/delta + 1``, ``eps = 1/20``, and at ``T = e^20``,
    ``m = 300``.

    Control: the rate ``pi/delta`` is sharp.  With ``2 pi/delta`` in its place
    both bounds exceed ``Lambda`` there.
    """
    delta, big_k, log_rho = pi / 4, 10**4, 1000.0
    big_n = 4 * big_k
    assert _in_arc(big_n, Fraction(1, 4), Fraction(1, 4)) >= big_k
    mass = big_n * log_rho
    for rate in (pi / delta, 2 * pi / delta):
        wide = _wide_bound(big_k, big_n, delta, log_rho, 20.0, 300, rate)
        const = _wide_const_bound(big_k, delta, pi / delta + 1, 1 / 20, log_rho, rate)
        if rate == pi / delta:
            assert mass >= wide and mass >= const
        else:
            assert mass < wide and mass < const


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


# Integer imitations of x^N - rho^N (lem:gaussbinom, prop:gausslow).

Gauss = tuple[int, int]  # a + bi


def _gmul(z: Gauss, w: Gauss) -> Gauss:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def _gpow(z: Gauss, n: int) -> Gauss:
    out = (1, 0)
    for _ in range(n):
        out = _gmul(out, z)
    return out


def _upper(box: int) -> list[Gauss]:
    return [(a, b) for a in range(-box, box + 1) for b in range(1, box + 1)]


def test_polynomials_in_a_power() -> None:
    """``lem:gaussbinom``: Gaussian ``alpha`` above the axis with one value of
    ``(alpha - t)^N`` number at most two, and differ by a unit.

    Control: ``x^4 + 4`` has two such roots, so "at most one" is false.
    """
    for n in range(1, 13):
        for t in range(-3, 4):
            classes: dict[Gauss, list[Gauss]] = {}
            for z in _upper(10):
                classes.setdefault(_gpow((z[0] - t, z[1]), n), []).append(z)
            for members in classes.values():
                assert len(members) <= 2
                (a, b), *rest = members
                for c, d in rest:
                    assert (c - t, d) in {(-(a - t), -b), (-b, a - t), (b, -(a - t))}
    assert _gpow((1, 1), 4) == _gpow((-1, 1), 4) == (-4, 0)
    assert _product([[2, -2, 1], [2, 2, 1]]) == [4, 0, 0, 0, 1]


def _inverse_series(p: Poly, m: int) -> list[Fraction]:
    """The first ``m`` coefficients of ``1/p`` at ``0``."""
    u = [Fraction(1, p[0])]
    for n in range(1, m):
        s = sum(p[k] * u[n - k] for k in range(1, min(n, len(p) - 1) + 1))
        u.append(-s / p[0])
    return u


def _lowest_denominator(p: Poly, m: int) -> int:
    """``d_m``: the least ``d > 0`` with ``d u_l`` integral for ``l < m``."""
    d = 1
    for c in _inverse_series(p, m):
        d = d * c.denominator // gcd(d, c.denominator)
    return d


def _pairs(roots: list[Gauss]) -> Poly:
    return _product([[a * a + b * b, -2 * a, 1] for a, b in roots])


#: Primitive Gaussian integers of pairwise coprime odd norms 5, 13, 17, 29.
COPRIME = [(1, 2), (-2, 3), (4, 1), (-5, 2)]


def test_lowest_coefficients_coprime() -> None:
    """``prop:gausslow``, items 1-2: ``d_m = P(0)^m``, and the multiple
    ``P (d_m/P mod x^m)`` is ``d_m`` below ``x^m``; random multiples pay
    ``P(0)^gap`` at their lowest coefficient, ``gap`` the distance to
    the next nonzero one."""
    rng = random.Random(SEED + 4)
    for big_k in range(1, len(COPRIME) + 1):
        p = _pairs(COPRIME[:big_k])
        for m in range(1, 6):
            d = _lowest_denominator(p, m)
            assert d == p[0] ** m
            q = [d * c for c in _inverse_series(p, m)]
            assert all(c.denominator == 1 for c in q)
            f = _mul(p, [int(c) for c in q])
            assert f[:m] == [d] + [0] * (m - 1)
            for _ in range(20):
                g = _mul(f, _cofactor(rng))
                low = next(i for i, c in enumerate(g) if c)
                gap = next(i for i, c in enumerate(g[low + 1 :], 1) if c)
                assert g[low] % p[0] ** gap == 0


def test_lowest_coefficients_common_norm() -> None:
    """``prop:gausslow``, item 3: at a common norm ``n``, ``d_m | n^(K+m-1)``.

    Control: there ``d_m < P(0)^m`` for ``K, m >= 2``, so item 2 needs its
    coprimality.
    """
    n = 5 * 13 * 17 * 29
    circle = [(a, b) for a, b in _upper(isqrt(n)) if a * a + b * b == n]
    assert len(circle) == 32
    for roots in ([(1, 8), (-1, 8), (4, 7), (-4, 7)], circle[:6]):
        norm = roots[0][0] ** 2 + roots[0][1] ** 2
        p = _pairs(roots)
        big_k = len(roots)
        for m in range(1, 6):
            d = _lowest_denominator(p, m)
            assert norm ** (big_k + m - 1) % d == 0
            if m >= 2:
                assert d < p[0] ** m


def _level_sets(big_b: int, degree: int, box: int) -> dict[tuple, list[Gauss]]:
    """Gaussian ``y`` above the axis grouped by the real value of ``g(y)``,
    over ``g`` with ``g(0) = 0``, positive leading coefficient and
    coefficients in ``[-B, B]``."""
    points = _upper(box)
    out: dict[tuple, list[Gauss]] = {}
    for s in range(1, degree + 1):
        for g in product(range(-big_b, big_b + 1), repeat=s):
            if g[-1] <= 0:
                continue
            for y in points:
                v = (0, 0)
                for c in reversed(g):
                    v = _gmul((v[0] + c, v[1]), y)
                if v[1] == 0:
                    out.setdefault((g, v[0]), []).append(y)
    return out


# Blocks and heavy coefficients at Gaussian roots (lem:gausscarry,
# lem:gaussblocks, thm:gausscharge, prop:gaussheavy).


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


def test_gaussian_blocks_and_heavy_coefficients() -> None:
    """``lem:gaussblocks`` and ``prop:gaussheavy``, item 1: the blocks tile
    ``f``, are multiples of ``P`` without a clean split, start with a heavy
    coefficient, and number at most the heavy nonleading coefficients; every
    split of a block is charged as in ``lem:gausscarry``, and each block pays
    ``thm:gausscharge``.  Heavy means ``|c| >= rho_min/2``, i.e.
    ``4c^2 >= n_min``."""
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
            assert abs(blk[0]) >= p[0] and 4 * blk[0] ** 2 >= n_min
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
        heavy = sum(4 * c * c >= n_min for c in _trim(f)[:-1])
        assert len(blocks) <= heavy


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


def _horner(f: Poly, z: Gauss) -> Gauss:
    return _tail(f, 0, z)


def test_one_heavy_coefficient_is_one_level_set() -> None:
    """``prop:gaussheavy``, item 2: ``b_2(F) < rho_min/2`` leaves one block
    ``v + H`` with ``H(alpha_j) = -v`` and ``(rho_min/2)^deg H <= |v|``.

    Checked at ``y^6 - 2y^4 + y^2 + 270400``, whose roots include
    ``+-7 + 4i`` and ``8i`` (the triple quoted after the proposition), and
    at every multiple ``g(x) - v`` with small coefficients whose Gaussian
    roots in a box have ``rho_min > 2B``.
    Control: at ``y^3 - 2y^2 + y + 100``, with root ``3 + 4i``,
    ``rho_min^3 > |v|``, so the degree bound fails with ``rho_min`` in place
    of ``rho_min/2``.
    """
    h = [0, 0, 1, 0, -2, 0, 1]
    roots = [(7, 4), (-7, 4), (0, 8)]
    v = -_horner(h, (0, 8))[0]
    f = [v] + h[1:]
    n_min = min(a * a + b * b for a, b in roots)
    assert n_min == 64 and v == 270400 and _divides(_pairs(roots), f)
    assert 4 * _b(f)[1] ** 2 < n_min
    assert _blocks(f, roots) == [(0, f)]
    assert all(_horner(h, z) == (-v, 0) for z in roots)
    assert n_min**6 <= 4**6 * v * v
    h, roots = [0, 1, -2, 1], [(3, 4)]
    v = -_horner(h, (3, 4))[0]
    f = [v] + h[1:]
    assert v == 100 and _divides(_pairs(roots), f) and 4 * _b(f)[1] ** 2 < 25
    assert _blocks(f, roots) == [(0, f)]
    assert 25**3 <= 4**3 * v * v
    assert 25**3 > v * v
    big_b = 2
    for (g, value), ys in _level_sets(big_b, 4, 6).items():
        n_min = min(a * a + b * b for a, b in ys)
        if 4 * big_b**2 >= n_min:
            continue
        f = [-value, *g]
        d = len(f) - 1
        assert _divides(_pairs(ys), f)
        assert _blocks(f, ys) == [(0, f)]
        assert n_min**d <= 4**d * value * value


# Counting Gaussian integers (cor:gausscount).


def test_gaussian_integers_in_a_disc() -> None:
    """Fewer than ``pi (X + 1)^2`` Gaussian integers have modulus below
    ``X``, checked with ``333/106 < pi`` for ``X = p/4``.

    Control: at ``X = 101/100`` there are five, more than ``pi X^2``
    (checked with ``22/7 > pi``), so the ``+1`` is needed.
    """
    for p in range(1, 200):
        x = Fraction(p, 4)
        r = ceil(x)
        count = sum(
            1
            for a in range(-r, r + 1)
            for b in range(-r, r + 1)
            if a * a + b * b < x * x
        )
        assert count <= Fraction(333, 106) * (x + 1) ** 2
    x = Fraction(101, 100)
    count = sum(1 for a in range(-2, 3) for b in range(-2, 3) if a * a + b * b < x * x)
    assert count == 5 > Fraction(22, 7) * x * x


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
