"""Exact checks of ``coefficient-mass-sectors.tex``.

Thin sectors and sectors of every width are checked on seeded random
Gaussian-integer multiples, with real zeros along the rays counted exactly by
Sturm sequences; the integer imitations of ``x^N - rho^N`` and the heavy
coefficients at Gaussian roots on seeded integer multiples.  Every group has
a control that a false variant of its statement is caught.  The polynomial
helpers and the block decomposition of ``lem:gaussblocks`` (a result of
``coefficient-mass-complex.tex``) are those of ``tests/test_complex.py``.
"""

from __future__ import annotations

import random
from fractions import Fraction
from itertools import product
from math import atan, ceil, exp, gcd, isqrt, log, log1p, pi, prod

import pytest

from tests.test_complex import (
    COPRIME,
    SEED,
    Gauss,
    Poly,
    _b,
    _block_multiples,
    _blocks,
    _cofactor,
    _divides,
    _gmul,
    _mul,
    _pairs,
    _product,
    _tail,
    _trim,
)

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


# Integer imitations of x^N - rho^N (lem:gaussbinom, prop:gausslow).


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


# Heavy coefficients at Gaussian roots (prop:gaussheavy).


def test_heavy_coefficients_bound_the_blocks() -> None:
    """``prop:gaussheavy``, item 1, on the multiples of ``test_gaussian_blocks``
    in ``tests/test_complex.py``: every block of ``lem:gaussblocks`` starts
    with a heavy coefficient, of modulus at least ``P(0)``, and the blocks
    number at most the heavy nonleading coefficients.  Heavy means
    ``|c| >= rho_min/2``, i.e. ``4c^2 >= n_min``."""
    rng = random.Random(SEED + 7)
    for _ in range(300):
        roots = COPRIME[: rng.randint(1, len(COPRIME))]
        n_min = min(a * a + b * b for a, b in roots)
        p = _pairs(roots)
        f = _block_multiples(rng, p)
        blocks = _blocks(f, roots)
        for _, blk in blocks:
            assert abs(blk[0]) >= p[0] and 4 * blk[0] ** 2 >= n_min
        heavy = sum(4 * c * c >= n_min for c in _trim(f)[:-1])
        assert len(blocks) <= heavy


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
