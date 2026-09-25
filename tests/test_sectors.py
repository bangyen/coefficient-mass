"""Exact checks of ``coefficient-mass-sectors.tex``.

Thin sectors and sectors of every width are checked on seeded random
Gaussian-integer multiples, with real zeros along the rays counted exactly by
Sturm sequences; the integer imitations of ``x^N - rho^N`` and the heavy
coefficients at Gaussian roots on seeded integer multiples; polynomials in a
power and symmetric root sets exactly; ``p``-adic Newton polygons at the primes
over coprime norms on seeded multiples, and small coefficients after the
lowest one by exhausting the cofactor.  Every group has
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
    _mass,
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


# Integer imitations of x^N - rho^N (lem:gaussbinom, prop:gausspower,
# prop:gausslow).


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


def _in_power(a: Poly, n: int) -> Poly:
    """``A(x^N)``."""
    out = [0] * (n * (len(a) - 1) + 1)
    out[::n] = a
    return out


def _norm(z: Gauss) -> int:
    return z[0] * z[0] + z[1] * z[1]


def test_polynomials_in_a_power_pay() -> None:
    """``prop:gausspower``, item 1: a multiple ``A(x^N)`` of ``P`` has
    ``Lambda >= (N/2) sum log rho_j``, that is ``exp(Lambda)^4 >= prod
    |alpha_j|^(2N)``, on the least such ``A`` (the product of the minimal
    polynomials of the classes of ``alpha_j^N``) and seeded multiples of it;
    equality at ``x^4 + 4k^4``.

    Control: the same with ``N`` for ``N/2`` fails at ``x^4 + 4``.
    """
    rng = random.Random(SEED + 9)
    points = _upper(6)
    for _ in range(150):
        n = rng.randint(1, 9)
        roots = rng.sample(points, rng.randint(1, 5))
        minimal: dict[Gauss, Poly] = {}
        for z in roots:
            u, v = _gpow(z, n)
            minimal[(u, abs(v))] = [-u, 1] if v == 0 else [u * u + v * v, -2 * u, 1]
        least = _product(list(minimal.values()))
        for a in (least, _mul(least, _cofactor(rng))):
            f = _in_power(a, n)
            assert _divides(_pairs(roots), f)
            assert _mass(f) ** 4 >= prod(_norm(z) ** n for z in roots)
    for k in range(1, 6):
        f = _in_power([4 * k**4, 1], 4)
        assert _divides(_pairs([(k, k), (-k, k)]), f)
        assert _mass(f) ** 4 == (2 * k * k) ** 8
    assert _mass([4, 0, 0, 0, 1]) ** 2 < 2**8


def _dihedral(a: int) -> list[Gauss]:
    """The four points of ``prop:gausspower``, item 3, at ``a``."""
    return [(a, a - 1), (-(a - 1), a), (-a, a - 1), (a - 1, a)]


def _within(z: Gauss, cot: Fraction) -> bool:
    """``|arg z - pi/2| <= delta`` for ``cot(delta) = cot``, ``Im z > 0``."""
    return abs(z[0]) * cot <= z[1]


def _log2_binomials(k: int) -> int:
    """The exponent ``(k-1)^2`` of 2 bounding ``prod_(0<j<k) binom(k, j)``."""
    return max(k - 1, 0) ** 2


def test_symmetric_root_sets() -> None:
    """``prop:gausspower``, items 2-3: root sets with ``-Z = Z`` (``iZ = Z``)
    make ``P`` a polynomial in ``x^2`` (``x^4``) with the stated mass bounds,
    on the families of item 3 in sectors with ``cot delta = 3, 1/2`` and on
    seeded symmetrized sets.

    Control: the families exceed half the stated leading terms, ``K^2/2 log
    rho_max`` and ``K^2/4 log rho_max``; and ``{alpha, i alpha, -conj(alpha)}``
    has ``i alpha_j`` among the roots for every ``j`` but ``iZ != Z``, and its
    ``P`` (``K = 3``) is not a polynomial in ``x^4``.
    """
    for s in range(1, 9):
        for big_r in (max(s, 3), 3 * s + 5, 40):
            if big_r < s:
                continue
            roots = [(e, c) for c in range(big_r, big_r + s) for e in (1, -1)]
            big_k = len(roots)
            assert all(_within(z, Fraction(3)) for z in roots)
            assert all(big_r**2 <= _norm(z) <= 4 * big_r**2 for z in roots)
            p = _pairs(roots)
            assert all(c == 0 for c in p[1::2])
            top = max(_norm(z) for z in roots)
            assert _mass(p) ** 2 <= top ** (big_k * (big_k + 1)) * 4 ** (
                big_k**2 - big_k
            )
            assert _mass(p) <= (2 * big_r) ** (big_k * (big_k + 1)) * 2 ** (
                big_k * (big_k - 1)
            )
            assert _mass(p) ** 4 > top ** (big_k * big_k)
            if big_r < 2:
                continue
            roots = [z for a in range(big_r, big_r + s) for z in _dihedral(a)]
            big_k = len(roots)
            assert len(set(roots)) == big_k
            assert all(_within(z, Fraction(1, 2)) for z in roots)
            assert all(big_r**2 <= _norm(z) <= 8 * big_r**2 for z in roots)
            p = _pairs(roots)
            assert all(c == 0 for i, c in enumerate(p) if i % 4)
            top = max(_norm(z) for z in roots)
            half = big_k // 2
            assert _mass(p) ** 2 <= top ** (2 * half * half + 2 * half) * 4 ** (
                _log2_binomials(half)
            )
            assert _mass(p) ** 2 <= (8 * big_r**2) ** (big_k**2 // 2 + big_k) * 2 ** (
                big_k**2 // 2
            )
            assert _mass(p) ** 8 > top ** (big_k * big_k)
    rng = random.Random(SEED + 10)
    for _ in range(40):
        base = rng.sample([(a, b) for a, b in _upper(9) if a > 0], rng.randint(1, 4))
        for roots, step in (
            ([z for a, b in base for z in ((a, b), (-a, b))], 2),
            ([z for a, b in base for z in ((a, b), (-b, a), (-a, b), (b, a))], 4),
        ):
            roots = list(dict.fromkeys(roots))
            big_k, p = len(roots), _pairs(roots)
            assert all(c == 0 for i, c in enumerate(p) if i % step)
            top = max(_norm(z) for z in roots)
            k = 2 * big_k // step
            assert _mass(p) ** 2 <= top ** (step * k * (k + 1) // 2) * 4 ** (
                _log2_binomials(k)
            )
    alpha = (2, 1)
    roots = [alpha, _gmul((0, 1), alpha), (-2, 1)]
    zset = set(roots) | {(a, -b) for a, b in roots}
    assert all(_gmul((0, 1), z) in zset for z in roots)
    assert any(_gmul((0, 1), z) not in zset for z in zset)
    assert any(c for i, c in enumerate(_pairs(roots)) if i % 4)


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


# Valuations at the primes over the norms (prop:gaussadic).

#: Odd, pairwise coprime norms ``125 = 5^3``, ``13``, ``17``, ``89`` with
#: ``gcd(a, c) = 1``: a prime power beside the primes of ``COPRIME``.
COPRIME_POWER = [(2, 11), (-2, 3), (4, 1), (8, 5)]


def _val(n: int, p: int) -> int:
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def _prime_powers(n: int) -> list[tuple[int, int]]:
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append((p, _val(n, p)))
            n //= p ** out[-1][1]
        p += 1
    return out + ([(n, 1)] if n > 1 else [])


def _slope_end(f: Poly, p: int, w: int) -> int | None:
    """The right endpoint of the edge of slope ``-w`` of the lower convex hull
    of the points ``(i, v_p(f_i))``, ``f_i != 0``, or ``None``."""
    pts = [(i, _val(c, p)) for i, c in enumerate(f) if c]
    hull: list[tuple[int, int]] = []
    for q in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (q[0] - x1) >= (q[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(q)
    for (x1, y1), (x2, y2) in zip(hull, hull[1:], strict=False):
        if y1 - y2 == w * (x2 - x1):
            return x2
    return None


def _adic_charge(f: Poly, roots: list[Gauss]) -> int:
    """``exp`` of the middle term of ``prop:gaussadic``, item 2, after
    checking item 1 at every ``(j, p)``."""
    support = [i for i, c in enumerate(f) if c]
    e2 = support[1]
    charge = 1
    for z in roots:
        for p, w in _prime_powers(_norm(z)):
            y = _slope_end(f, p, w)
            assert y is not None and y >= e2 and f[y]
            assert all(f[i] % p ** (w * (y - i)) == 0 for i in range(y))
            charge *= p ** (w * sum(y - i for i in support if i < y))
    return charge


def _power_multiple(roots: list[Gauss], n: int) -> Poly:
    """The least ``A(x^N)`` divisible by ``P``: ``A`` the product of the
    minimal polynomials of the classes of ``alpha_j^N``."""
    minimal: dict[Gauss, Poly] = {}
    for z in roots:
        u, v = _gpow(z, n)
        minimal[(u, abs(v))] = [-u, 1] if v == 0 else [u * u + v * v, -2 * u, 1]
    return _in_power(_product(list(minimal.values())), n)


def test_valuations_at_the_norms() -> None:
    """``prop:gaussadic``, items 1-2: at every ``(j, p)`` the ``p``-adic
    Newton polygon has an edge of slope ``-v_p(n_j)`` ending at a nonzero
    ``f_y`` with ``y >= e_2``, ``p^(w(y-i)) | f_i`` below it, and ``Lambda``
    bounds the charge, which is at least ``P(0)^(e_2 - e)``; on seeded
    multiples at ``COPRIME`` and ``COPRIME_POWER``, polynomials in ``x^N``
    (which pay ``P(0)^N``), and ``P``, where the charge is ``P(0)``.

    Control: ``p^(w(y-i)+1) | f_i`` fails at ``F = P``, ``i = 0``.
    """
    rng = random.Random(SEED + 11)
    for base in (COPRIME, COPRIME_POWER):
        for big_k in range(1, len(base) + 1):
            roots = base[:big_k]
            p = _pairs(roots)
            assert _adic_charge(p, roots) == p[0]
            for _ in range(40):
                f = _block_multiples(rng, p)
                f = [0] * rng.randint(0, 2) + f
                support = [i for i, c in enumerate(f) if c]
                charge = _adic_charge(f, roots)
                assert _mass(f) >= charge >= p[0] ** (support[1] - support[0])
            for n in range(1, 6):
                f = _power_multiple(roots, n)
                assert _divides(p, f)
                assert _mass(f) >= _adic_charge(f, roots) >= p[0] ** n
    p = _pairs(COPRIME)
    for z in COPRIME:
        for q, w in _prime_powers(_norm(z)):
            assert _slope_end(p, q, w) == 1
            assert p[0] % q ** (w + 1) != 0


def _light_run(p: Poly, m: int, v: int, limit: int) -> Poly | None:
    """A multiple ``P S`` with ``0 < s_0 <= limit`` and ``|f_i| <= V`` for
    ``0 < i < m``, found by exhausting the ``s_k`` in turn, least ``s_0``
    first."""
    for s0 in range(1, limit + 1):
        stack = [[s0]]
        while stack:
            s = stack.pop()
            k = len(s)
            if k == m:
                return _mul(p, s)
            c = sum(p[i] * s[k - i] for i in range(1, min(k, len(p) - 1) + 1))
            stack.extend(
                [*s, t] for t in range(-((v + c) // p[0]), (v - c) // p[0] + 1)
            )
    return None


def test_small_coefficients_after_the_lowest() -> None:
    """``prop:gaussadic``, item 3: some multiple has ``|f_i| <= V`` for
    ``0 < i < m`` and ``P(0) <= |f_0| <= P(0)^m / V^(m-1)``, at ``COPRIME``,
    ``K <= 3``, ``m <= 3``; the least such ``|f_0|`` is exhibited.

    Control: already at ``K = 2``, ``m = 3``, ``V = 2`` the least ``|f_0|``
    is ``18330 < P(0)^3``, so ``prop:gausslow``, item 2, fails with small
    coefficients in place of zeros.
    """
    for big_k in range(1, 4):
        p = _pairs(COPRIME[:big_k])
        for m in range(1, 4):
            for v in (1, 2, 5, 20):
                if v >= p[0]:
                    continue
                bound = p[0] ** m // v ** (m - 1)
                f = _light_run(p, m, v, bound // p[0])
                assert f is not None and _divides(p, f)
                assert p[0] <= f[0] <= bound and len(f) <= m + 2 * big_k
                assert all(abs(c) <= v for c in f[1:m])
    p = _pairs(COPRIME[:2])
    f = _light_run(p, 3, 2, p[0] ** 2)
    assert f is not None and f[0] == 18330 < p[0] ** 3


def _newton_root(p: Poly, m: int) -> int:
    """``t`` with ``P(0) | t`` and ``P(t) = 0 mod P(0)^m``, by Newton's
    method from ``0`` as in the proof of ``prop:gausscong``."""
    d, t = p[0], 0
    mod = d**m
    for _ in range(m):
        value = sum(c * t**i for i, c in enumerate(p))
        slope = sum(i * c * t ** (i - 1) for i, c in enumerate(p) if i)
        t = (t - value * pow(slope, -1, mod)) % mod
    return t


def _in_lattice(p: Poly, f: list[int]) -> bool:
    """Whether ``f`` is the lowest ``len(f)`` coefficients of a multiple of
    ``P``: ``f/P mod x^m`` has integer coefficients (``prop:gausslow``)."""
    u = _inverse_series(p, len(f))
    return all(
        sum(f[i] * u[n - i] for i in range(n + 1)).denominator == 1
        for n in range(len(f))
    )


def test_one_congruence() -> None:
    """``prop:gausscong``, items 1-2, at ``COPRIME``, ``K <= 4``, ``m <= 4``:
    the lowest ``m`` coefficients of the multiples are exactly the ``f`` with
    ``sum f_i t^i = 0 mod P(0)^m``, on the lattice basis and on seeded
    random vectors, half of them adjusted into the congruence; at ``m = 2``,
    ``P(0) | f_0`` and ``f_1 = P'(0) f_0/P(0) mod P(0)``.

    Control: at the common norm ``5`` (roots ``1 + 2i``, ``2 + i``),
    ``gcd(P(0), P'(0)) = 5`` and ``d_2 < P(0)^2``, so item 1 needs the
    hypothesis.
    """
    rng = random.Random(SEED + 11)
    for big_k in range(1, len(COPRIME) + 1):
        p = _pairs(COPRIME[:big_k])
        d = p[0]
        assert gcd(d, p[1]) == 1
        for m in range(1, 5):
            t = _newton_root(p, m)
            mod = d**m
            assert t % d == 0
            assert sum(c * t**i for i, c in enumerate(p)) % mod == 0

            def congruent(f: list[int], t: int = t, mod: int = mod) -> bool:
                return sum(c * t**i for i, c in enumerate(f)) % mod == 0

            for k in range(m):
                row = ([0] * k + p)[:m]
                row += [0] * (m - len(row))
                assert congruent(row) and _in_lattice(p, row)
            for trial in range(60):
                f = [rng.randint(-(d**m), d**m) for _ in range(m)]
                if trial % 2:
                    f[0] -= sum(c * t**i for i, c in enumerate(f)) % mod
                assert congruent(f) == _in_lattice(p, f)
            if m == 2:
                for _ in range(60):
                    f = [d * rng.randint(-50, 50), rng.randint(-(d**2), d**2)]
                    f[0] += rng.choice([0, 0, 1])
                    item2 = f[0] % d == 0 and (f[1] - p[1] * (f[0] // d)) % d == 0
                    assert item2 == _in_lattice(p, f)
    p = _pairs([(1, 2), (2, 1)])
    assert gcd(p[0], p[1]) == 5
    assert _lowest_denominator(p, 2) < p[0] ** 2


def test_small_derivative_at_zero() -> None:
    """``prop:gausscong``, item 3: at ``-26 + 35i``, ``-1 + 60i``,
    ``29 + 62i``, ``47 + 62i`` the norms are odd and pairwise coprime,
    ``gcd(a_j, c_j) = 1``, ``43 < rho_j < 78`` and ``P'(0) = 6``, so
    ``F = P`` has ``|f_1| < rho_min/2`` and forces ``C > 3.77`` at ``m = 2``.

    Control: moving one point to ``48 + 62i`` makes ``|P'(0)|`` exceed
    ``rho_min/2`` by far.
    """
    roots = [(-26, 35), (-1, 60), (29, 62), (47, 62)]
    norms = [_norm(z) for z in roots]
    assert norms == [1901, 3601, 4685, 6053]
    assert all(n % 2 and gcd(a, c) == 1 for (a, c), n in zip(roots, norms, strict=True))
    assert all(gcd(x, y) == 1 for i, x in enumerate(norms) for y in norms[i + 1 :])
    assert all(43**2 < n < 78**2 for n in norms)
    p = _pairs(roots)
    assert p[0] == prod(norms) == 194126805235805 and p[1] == 6
    assert 4 * p[1] ** 2 < min(norms)
    assert log(p[0]) / log(max(norms)) > 3.77
    q = _pairs([(-26, 35), (-1, 60), (29, 62), (48, 62)])
    assert 4 * q[1] ** 2 > 10**6 * min(_norm(z) for z in roots)


QGauss = tuple[Fraction, Fraction]


def _qmul(a: QGauss, b: QGauss) -> QGauss:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _on_lines(lines: list[tuple[Gauss, Gauss]], s: int) -> list[Gauss]:
    """The points ``lambda_j s + mu_j``, conjugated into the upper half-plane."""
    out = []
    for (lr, li), (mr, mi) in lines:
        a, c = lr * s + mr, li * s + mi
        out.append((a, abs(c)))
    return out


def _line_residues(lines: list[tuple[Gauss, Gauss]]) -> list[QGauss]:
    """``Lambda Q'(w_j)/lambda_j`` of ``prop:gaussline``, item 1."""
    ws = []
    for lam, mu in lines:
        n = _norm(lam)
        ws.append(
            _qmul(
                (Fraction(-mu[0]), Fraction(-mu[1])),
                (Fraction(lam[0], n), Fraction(-lam[1], n)),
            )
        )
    big_l = prod(_norm(lam) for lam, _ in lines)
    out = []
    for j, (lam, _) in enumerate(lines):
        w = ws[j]
        q: QGauss = (Fraction(0), 2 * w[1])
        for k, v in enumerate(ws):
            if k != j:
                q = _qmul(
                    q, _qmul((w[0] - v[0], w[1] - v[1]), (w[0] - v[0], w[1] + v[1]))
                )
        n = _norm(lam)
        q = _qmul(q, (Fraction(lam[0], n), Fraction(-lam[1], n)))
        out.append((big_l * q[0], big_l * q[1]))
    return out


LINES_2 = [((-1, 1), (-3, 2)), ((1, 1), (1, 2))]
LINES_3 = [((-1, 1), (-3, 2)), ((0, 1), (-1, 1)), ((1, 1), (-1, 0))]


def _meets_gausslow(roots: list[Gauss]) -> bool:
    """The hypotheses of ``prop:gausslow``, item 2: distinct points above the
    axis with odd, pairwise coprime norms and ``gcd(a_j, c_j) = 1``."""
    norms = [_norm(z) for z in roots]
    return (
        len(set(roots)) == len(roots)
        and all(c > 0 and gcd(a, c) == 1 for a, c in roots)
        and all(n % 2 for n in norms)
        and all(gcd(x, y) == 1 for i, x in enumerate(norms) for y in norms[i + 1 :])
    )


def test_constant_derivative_along_lines() -> None:
    """``prop:gaussline``: on the lines of items 2 and 3, ``P'(0) = 4`` and
    ``90`` at every ``s`` in a window, ``P(0) = Lambda Q(s)``, and
    ``Lambda Q'(w_j) = N lambda_j`` with ``N = -P'(0)`` (item 1); the
    hypotheses of ``prop:gausslow``, item 2, hold for every ``s >= -1`` on
    item 2 and exactly for odd ``s = 0, 3 mod 5`` on item 3; at
    ``s = 10^6 + 5`` the points of item 3 are in one annulus, ``|P'(0)| <
    rho_min/2`` and ``log P(0)/(2 log rho_max) > 2.97``.

    Control: moving ``mu_2`` of item 3 to ``-1 + 2i`` makes ``P'(0)`` move
    with ``s`` and item 1's residues unequal.
    """
    for lines, value in ((LINES_2, 4), (LINES_3, 90)):
        residues = _line_residues(lines)
        assert residues == [(Fraction(-value), Fraction(0))] * len(lines)
        big_l = prod(_norm(lam) for lam, _ in lines)
        for s in range(-1, 120):
            roots = _on_lines(lines, s)
            p = _pairs(roots)
            assert p[1] == value
            q = Fraction(1)
            for (lr, li), (mr, mi) in lines:
                q *= Fraction(
                    (lr * s + mr) ** 2 + (li * s + mi) ** 2, lr * lr + li * li
                )
            assert p[0] == big_l * q
            if lines is LINES_2:
                assert _meets_gausslow(roots)
            elif s >= 1:
                assert _meets_gausslow(roots) == (s % 2 == 1 and s % 5 in (0, 3))
    s = 10**6 + 5
    roots = _on_lines(LINES_3, s)
    norms = [_norm(z) for z in roots]
    p = _pairs(roots)
    assert _meets_gausslow(roots) and 4 * p[1] ** 2 < min(norms) < max(norms) < 4 * min(
        norms
    )
    assert log(p[0]) / log(max(norms)) > 2.97
    moved = [LINES_3[0], ((0, 1), (-1, 2)), LINES_3[2]]
    assert len({_pairs(_on_lines(moved, s))[1] for s in range(5)}) > 1
    assert len(set(_line_residues(moved))) > 1


def test_light_multiples() -> None:
    """``prop:gausslight`` on the Pell level sets ``(8c^3 + 2c)^2 +
    (y^3 - y)^2``, which are light: ``d = 6 >= 2K``, ``|f_e| < rho_min^(d+1)``,
    and a constant ``C`` for the step at ``m = d + 1`` needs ``C log rho_max >
    log P(0) - log rho_min >= (2K - 1) log rho_min``.

    Control: ``|f_e| < rho_min^d`` fails on every one of them.
    """
    h = [0, 0, 1, 0, -2, 0, 1]
    for a, c in _pell_triples(8):
        roots = [(a, c), (-a, c), (0, 2 * c)]
        f = [(8 * c**3 + 2 * c) ** 2] + h[1:]
        p = _pairs(roots)
        assert _divides(p, f)
        n_min, n_max = min(_norm(z) for z in roots), max(_norm(z) for z in roots)
        assert all(4 * x * x < n_min for x in f[1:])
        d = len(f) - 1
        assert d >= 2 * len(roots)
        assert f[0] ** 2 < n_min ** (d + 1)
        assert f[0] ** 2 > n_min**d
        c_min = (log(p[0]) - log(f[0]) / (d + 1)) / (0.5 * log(n_max))
        assert c_min * 0.5 * log(n_max) > log(p[0]) - 0.5 * log(n_min)
        assert log(p[0]) - 0.5 * log(n_min) >= (2 * len(roots) - 1) * 0.5 * log(n_min)


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


def _pell_triples(count: int) -> list[tuple[int, int]]:
    """``(a, c)`` with ``a + c sqrt 3 = (2 + sqrt 3)^n``, ``n = 2, 3, ...``."""
    out, (a, c) = [], (7, 4)
    for _ in range(count):
        out.append((a, c))
        a, c = 2 * a + 3 * c, a + 2 * c
    return out


def test_three_points_at_every_scale() -> None:
    """After ``prop:gaussheavy``: at ``a^2 - 3c^2 = 1``, ``c >= 4``,
    ``(y^3 - y)^2 = -(8c^3 + 2c)^2`` at ``+-a + ci`` and ``2ci``, which have
    ``rho_min = 2c > 4``, and ``y^3 - y - (8c^3 + 2c)i`` factors as quoted.

    Control: at ``(a, c) = (8, 4)``, off the Pell equation, ``8 + 4i`` is
    not in the level set.
    """
    h = [0, 0, 1, 0, -2, 0, 1]
    for a, c in _pell_triples(8):
        assert a * a - 3 * c * c == 1 and c >= 4
        k = 8 * c**3 + 2 * c
        roots = [(a, c), (-a, c), (0, 2 * c)]
        assert all(_horner([0, -1, 0, 1], z) == (0, k) for z in roots[:2])
        assert _horner([0, -1, 0, 1], roots[2]) == (0, -k)
        assert all(_horner(h, z) == (-k * k, 0) for z in roots)
        f = [k * k] + h[1:]
        n_min = min(x * x + y * y for x, y in roots)
        assert n_min == 4 * c * c and 4 * _b(f)[1] ** 2 < n_min
        assert _divides(_pairs(roots), f)
        cubic = [(0, -k), (-1, 0), (0, 0), (1, 0)]
        fiber = [(a, c), (-a, c), (0, -2 * c)]
        linear = [[(-x, -y), (1, 0)] for x, y in fiber]
        assert _gpoly_product(linear) == cubic
    assert _pell_triples(1) == [(7, 4)] and 8 * 4**3 + 2 * 4 == 520
    assert _horner(h, (8, 4)) != _horner(h, (0, 8))


def _circle_q_lower(n: int) -> Fraction:
    """A rational lower bound for ``Q = (3 rho - 2)/(rho - 2)``,
    ``rho = sqrt n > 2``, which decreases in ``rho``."""
    rho_up = Fraction(isqrt(n * 10**12) + 1, 10**6)
    return (3 * rho_up - 2) / (rho_up - 2)


def _near_one_circle(h: Poly, roots: list[Gauss], ratio: Fraction | None) -> bool:
    """``(rho_j / rho_min)^d < Q`` for every root, with ``Q`` replaced by
    ``ratio`` when given, and ``K < 6 rho_min``."""
    norms = [a * a + b * b for a, b in roots]
    n_min, d = min(norms), len(h) - 1
    q = _circle_q_lower(n_min) if ratio is None else ratio
    return (
        all(Fraction(m, n_min) ** d < q * q for m in norms)
        and len(roots) ** 2 < 36 * n_min
    )


def test_level_set_near_one_circle() -> None:
    """``prop:gausscircle``: the prescribed roots of ``v + H`` have
    ``rho_min <= rho_j < rho_min Q^(1/d)`` and number fewer than
    ``6 rho_min``; checked on the Pell triples, on the level sets of
    ``test_one_heavy_coefficient_is_one_level_set``, and on the arithmetic
    that closes the proof, ``K < 5.8 rho`` once ``d >= 12 rho``.

    Control: ``Q = 1``, all the roots on one circle, fails at
    ``+-7 + 4i``, ``8i``.
    """
    h = [0, 0, 1, 0, -2, 0, 1]
    for a, c in _pell_triples(8):
        assert _near_one_circle(h, [(a, c), (-a, c), (0, 2 * c)], None)
    big_b, seen = 2, 0
    for (g, _), ys in _level_sets(big_b, 4, 6).items():
        if 4 * big_b**2 < min(a * a + b * b for a, b in ys):
            assert _near_one_circle([0, *g], ys, None)
            seen += 1
    assert seen > 0
    for n in range(5, 20000):
        rho = n**0.5
        q, d = (3 * rho - 2) / (rho - 2), 12 * rho
        count = (
            pi
            / 2
            * (rho * rho * (q ** (2 / d) - 1) + 2**0.5 * rho * (1 + q ** (1 / d)))
        )
        assert count < 5.8 * rho
    assert not _near_one_circle(h, [(7, 4), (-7, 4), (0, 8)], Fraction(1))


def test_gaussian_integers_in_a_half_annulus() -> None:
    """``prop:gausscircle``: fewer than
    ``(pi/2)(r'^2 - r^2 + sqrt 2 (r + r'))`` Gaussian integers above the axis
    have ``r <= |z| < r'``, checked with ``333/106 < pi`` and
    ``1414/1000 < sqrt 2``.

    Control: without the ``sqrt 2`` term the bound fails at ``r = 5``,
    ``r' = 501/100``, where ``3 + 4i``, ``4 + 3i``, ``5i`` and their
    reflections give five points (checked with ``22/7 > pi``).
    """
    for p in range(9, 120):
        r = Fraction(p, 4)
        for w in (Fraction(1, 100), Fraction(1, 3), Fraction(2), Fraction(p, 8)):
            s = r + w
            m = ceil(s)
            count = sum(
                1
                for a in range(-m, m + 1)
                for b in range(1, m + 1)
                if r * r <= a * a + b * b < s * s
            )
            bound = s * s - r * r + Fraction(1414, 1000) * (r + s)
            assert count <= Fraction(333, 212) * bound
    r, s = Fraction(5), Fraction(501, 100)
    count = sum(
        1 for a in range(-6, 7) for b in range(1, 7) if r * r <= a * a + b * b < s * s
    )
    assert count == 5 > Fraction(22, 14) * (s * s - r * r)


# Primes of a level set (prop:gaussprimes).


def _factor(n: int) -> dict[int, int]:
    out, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def _ord(n: int, p: int) -> int:
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def _gauss_prime(p: int) -> Gauss:
    """A Gaussian prime above ``p``: ``1 + i`` for 2, ``p`` if
    ``p = 3 mod 4``, and ``x + yi`` with ``x^2 + y^2 = p`` otherwise
    (Hermite-Serret)."""
    if p == 2:
        return (1, 1)
    if p % 4 == 3:
        return (p, 0)
    g = 2
    while pow(g, (p - 1) // 2, p) != p - 1:
        g += 1
    a, b = p, pow(g, (p - 1) // 4, p)
    while b * b > p:
        a, b = b, a % b
    y = isqrt(p - b * b)
    assert b * b + y * y == p
    return (b, y)


def _root_orders(z: Gauss, p: int) -> list[Fraction]:
    """``ord_p`` of ``z`` and of its conjugate under an embedding of
    ``Q(i)`` in ``C_p``, with ``ord_p(p) = 1``."""
    pi = _gauss_prime(p)
    norm = pi[0] ** 2 + pi[1] ** 2
    scale = Fraction(1, 2) if p == 2 else Fraction(1)
    out = []
    for w in (z, (z[0], -z[1])):
        k = 0
        while True:
            u = _gmul(w, (pi[0], -pi[1]))
            if u[0] % norm or u[1] % norm:
                break
            w, k = (u[0] // norm, u[1] // norm), k + 1
        out.append(k * scale)
    return out


def _first_edge(f: Poly, roots: list[Gauss]) -> bool:
    """``prop:gaussprimes``, item 1, for any ``f`` with ``f(0) != 0`` and
    Gaussian roots ``alpha_j`` above the axis, ``ell`` its least positive
    exponent: at each prime ``p`` of a norm, at most ``ell`` of the ``2K``
    numbers ``alpha_j``, ``conj(alpha_j)`` have ``ord_p > t_p =
    ord_p(f_ell)``, all with ``ord_p = s_p = (ord_p f(0) - t_p)/ell``."""
    ell = next(i for i in range(1, len(f)) if f[i])
    for p in sorted({p for a, c in roots for p in _factor(a * a + c * c)}):
        t = _ord(f[ell], p)
        s = Fraction(_ord(f[0], p) - t, ell)
        big = [o for z in roots for o in _root_orders(z, p) if o > t]
        if len(big) > ell or any(o != s for o in big):
            return False
    return True


def _prime_orders(f: Poly, roots: list[Gauss]) -> bool:
    """``prop:gaussprimes`` for ``f = v + H``: item 1, and item 2 when
    ``h_ell`` is not the leading coefficient: ``ord_p(n_j) > 2 t_p`` forces
    ``ord_p(n_j) = 2 s_p`` or ``s_p <= ord_p(n_j) <= s_p + t_p``, every norm
    has such a prime, and at most ``ell`` of the ``alpha_j`` share a
    norm."""
    f = _trim(f)
    ell = next(i for i in range(1, len(f)) if f[i])
    if not _first_edge(f, roots):
        return False
    if ell == len(f) - 1:
        return True
    norms = [a * a + c * c for a, c in roots]
    witnessed = set()
    for p in sorted({p for n in norms for p in _factor(n)}):
        t = _ord(f[ell], p)
        s = Fraction(_ord(f[0], p) - t, ell)
        for n in norms:
            e = _ord(n, p)
            if e > 2 * t:
                if not (e == 2 * s or s <= e <= s + t):
                    return False
                witnessed.add(n)
    return set(norms) <= witnessed and all(norms.count(n) <= ell for n in norms)


def test_primes_of_a_level_set() -> None:
    """``prop:gaussprimes`` on the Pell triples (``ell = 2``: the pair
    ``+-a + ci`` shares a norm, ``2ci`` is alone), on the pairs ``+-c + ai``
    of one norm where ``(y^3 + y)^2 = (8c^3 + 2c)^2``, which attain item 3,
    on the level sets of ``test_one_heavy_coefficient_is_one_level_set``,
    and, for item 1, which holds for every integer polynomial with nonzero
    constant term, on seeded multiples, even multiples and multiples in
    ``y^4`` of products of Gaussian pairs.

    Controls: at ``y^2 - 10y + 650``, with roots ``5 +- 25i``, two roots
    have positive ``ord_5`` though ``ell = 1``, so the threshold ``t_5 = 1``
    is needed; and the Pell triples have ``K = 3 > ell``, so item 3 needs
    one norm.
    """
    h = [0, 0, 1, 0, -2, 0, 1]
    h_rot = [0, 0, 1, 0, 2, 0, 1]
    for a, c in _pell_triples(8):
        k = 8 * c**3 + 2 * c
        roots = [(a, c), (-a, c), (0, 2 * c)]
        assert _prime_orders([k * k] + h[1:], roots)
        assert len(roots) == 3 > 2 and len({x * x + y * y for x, y in roots}) == 2
        pair = [(c, a), (-c, a)]
        assert all(_horner(h_rot, z) == (k * k, 0) for z in pair)
        assert 4 * 2**2 < a * a + c * c
        assert _prime_orders([-k * k] + h_rot[1:], pair)
    big_b, seen = 2, 0
    for (g, value), ys in _level_sets(big_b, 4, 6).items():
        if 4 * big_b**2 < min(a * a + b * b for a, b in ys):
            assert _prime_orders([-value, *g], ys)
            seen += 1
    assert seen > 0
    rng, ells = random.Random(SEED + 11), set()
    box = [(a, c) for a in range(-9, 10) for c in range(1, 10) if a]
    for _ in range(150):
        s = rng.sample(box, rng.randint(1, 3))
        q = [rng.randint(-6, 6) for _ in range(rng.randint(1, 4))]
        if q[0] == 0:
            q[0] = 1
        sym = sorted(set(s) | {(-a, c) for a, c in s})
        rot = {
            w
            for a, c in s
            for w in ((a, c), (-a, c), (c, a), (-c, a), (c, -a), (-c, -a))
            if w[1] > 0
        }
        rot = sorted(rot)
        q2 = [x for y in q for x in (y, 0)][:-1]
        for f, roots in (
            (_mul(_pairs(s), q), s),
            (_mul(_pairs(sym), q2), sym),
            (_pairs(rot), rot),
        ):
            assert f[0] != 0 and _divides(_pairs(roots), f)
            assert _first_edge(f, roots)
            ells.add(next(i for i in range(1, len(f)) if f[i]))
    assert {1, 2, 4} <= ells
    assert [o > 0 for o in _root_orders((7, 4), 5) + _root_orders((-7, 4), 5)].count(
        True
    ) == 2
    f, roots = _pairs([(5, 25)]), [(5, 25)]
    assert f == [650, -10, 1]
    assert _root_orders((5, 25), 5) == [1, 1] and _ord(f[1], 5) == 1
    assert sum(o > 0 for o in _root_orders((5, 25), 5)) == 2 > 1
    assert _prime_orders(f, roots)


# Symmetries of a level set (prop:gausssym).

_UNITS: list[Gauss] = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def _class(z: Gauss) -> frozenset[Gauss]:
    """The eight numbers ``u z``, ``u conj(z)``, ``u^4 = 1``."""
    return frozenset(_gmul(u, w) for u in _UNITS for w in (z, (z[0], -z[1])))


def _symmetries(h: Poly) -> list[Gauss]:
    """The units ``u`` with ``H(uy) = H(y)``, from the coefficients."""
    return [
        u
        for k, u in enumerate(_UNITS)
        if all(c == 0 for j, c in enumerate(h) if j and (j * k) % 4)
    ]


def _level_set_symmetric(h: Poly, roots: list[Gauss]) -> bool:
    """``prop:gausssym``, items 1 and 2, for ``v + H`` with the Gaussian
    roots ``roots`` above the axis: a unit taking one root of modulus at
    least ``rho_min`` to another is a symmetry of ``H``, and each class holds
    at most ``|U|`` of the roots."""
    value = _horner(h, roots[0])
    sym = _symmetries(h)
    for z in roots:
        for u in _UNITS:
            if _horner(h, _gmul(u, z)) == value and u not in sym:
                return False
    classes: dict[frozenset[Gauss], int] = {}
    for z in roots:
        classes[_class(z)] = classes.get(_class(z), 0) + 1
    return all(c <= len(sym) for c in classes.values())


def _pell_powers(k: int) -> list[tuple[Poly, Poly, list[Gauss], list[Gauss], int]]:
    """``(y^3 + y)^(2k)`` and ``(y^3 - y)^(2k)`` with the Pell pair
    ``+-c + ai`` and triple ``+-a + ci``, ``2ci``, for the first Pell ``c``
    above ``binom(2k, k)``."""
    out = []
    for a, c in _pell_triples(12):
        if c * c <= max(_power([0, 1, 0, 1], 2 * k)) ** 2:
            continue
        out.append(
            (
                _power([0, 1, 0, 1], 2 * k),
                _power([0, -1, 0, 1], 2 * k),
                [(c, a), (-c, a)],
                [(a, c), (-a, c), (0, 2 * c)],
                8 * c**3 + 2 * c,
            )
        )
        if len(out) == 2:
            break
    return out


def _power(p: Poly, k: int) -> Poly:
    out: Poly = [1]
    for _ in range(k):
        out = _mul(out, p)
    return out


def _pattern_classes(n: int) -> list[tuple[int, int]]:
    """For every choice of ``s_p`` at the primes ``p = 1 mod 4`` dividing
    ``n`` (all of them informative), the number of classes met by the
    Gaussian integers of norm ``n`` whose exponent of ``pi_p`` is ``s_p`` or
    ``e_p - s_p``, and ``m``, the number of ``p`` with ``e_p != 2 s_p``."""
    split = [(p, e) for p, e in _factor(n).items() if p % 4 == 1]
    r = isqrt(n)
    points = [
        (a, sign * isqrt(n - a * a))
        for a in range(-r, r + 1)
        for sign in (1, -1)
        if isqrt(n - a * a) ** 2 == n - a * a
    ]
    exps = {z: [_root_orders(z, p)[0] for p, _ in split] for z in points}
    out = []
    for s in product(*[range(e + 1) for _, e in split]):
        classes = {
            _class(z)
            for z in points
            if all(
                x in (sp, e - sp)
                for x, sp, (_, e) in zip(exps[z], s, split, strict=True)
            )
        }
        m = sum(e != 2 * sp for sp, (_, e) in zip(s, split, strict=True))
        out.append((len(classes), m))
    return out


def test_symmetries_of_a_level_set() -> None:
    """``prop:gausssym``: the powers ``(y^3 +- y)^(2k)`` put ``ell = 2k`` on
    the Pell pair and triple with nonleading coefficients below ``c``;
    items 1 and 2 on them, on every level set of even ``H`` of degree up to
    8 and of any ``H`` of degree up to 4 with coefficients in ``[-2, 2]``
    and roots in a box; the two bounds that close item 1 for ``u = +-i``,
    in rationals; and
    item 3's count of classes at every norm up to 1500.

    Controls: ``y^5 + y^4 + 6y^3 + 6y^2 + 25y`` is ``-25`` at ``+-(1 + 2i)``
    and not even, so item 1 needs small coefficients; with ``b < rho/2`` in
    place of ``b <= 1`` the bound for ``u = +-i`` fails at ``rho^2 = 5``;
    and without the valuations, the Gaussian integers of norm 125 meet two
    classes.
    """
    for k in (1, 2, 3):
        plus, minus, pair, triple, w = _pell_powers(k)[0]
        c = pair[0][0]
        assert plus[2 * k] == minus[2 * k] ** 2 == 1 and not any(plus[: 2 * k])
        assert max(abs(x) for x in plus[:-1] + minus[:-1]) < c
        assert all(_horner(plus, z) == (w ** (2 * k), 0) for z in pair)
        assert all(_horner(minus, z) == ((-1) ** k * w ** (2 * k), 0) for z in triple)
        assert 4 * c * c < min(_norm(z) for z in pair) == 4 * c * c + 1
        assert 4 * max(abs(x) for x in minus[:-1]) ** 2 < min(map(_norm, triple))
        assert _level_set_symmetric(plus, pair) and _level_set_symmetric(minus, triple)
        assert _class(pair[0]) == _class(pair[1]) and len(_symmetries(plus)) == 2
    big_b, seen = 2, 0
    level: dict[tuple, list[Gauss]] = {}
    for s in (3, 4):
        for g in product(range(-big_b, big_b + 1), repeat=s):
            if g[-1] <= 0:
                continue
            h = [0] + [x for c in g for x in (0, c)]
            for z in _upper(12):
                val = _horner(h, z)
                if val[1] == 0:
                    level.setdefault((tuple(h), val[0]), []).append(z)
    for (g, value), ys in _level_sets(big_b, 4, 6).items():
        level[((0, *g), value)] = ys
    for (h, _), ys in level.items():
        if 4 * big_b**2 < min(map(_norm, ys)):
            assert _level_set_symmetric(list(h), ys)
            seen += len(ys) > 1
    assert seen > 0
    r2 = Fraction(1415, 1000)
    x = Fraction(3536, 10000)
    assert x * x * 8 >= 1 and r2 * r2 >= 2
    assert (r2 + x + x**3) / (2 * (1 - x**4)) < Fraction(93, 100)
    x5 = Fraction(4473, 10000)
    assert x5 * x5 * 5 >= 1
    assert (r2 * x5 + Fraction(1, 5) + Fraction(1, 25)) / (1 - Fraction(1, 25)) < (
        Fraction(91, 100)
    )
    for n in range(5, 1500):
        for count, m in _pattern_classes(n):
            if count:
                assert count <= max(2 ** (m - 1), 1)
    h = [0, 25, 6, 6, 1, 1]
    assert _horner(h, (1, 2)) == _horner(h, (-1, -2)) == (-25, 0)
    assert _symmetries(h) == [(1, 0)]
    assert not _level_set_symmetric(h, [(1, 2)])
    r2_low, x5_low = Fraction(1414, 1000), Fraction(4472, 10000)
    assert x5_low * x5_low * 5 <= 1
    bound = (r2_low + x5_low + x5_low**3) / (2 * (1 - Fraction(1, 25)))
    assert bound > 1
    norm125 = {_class(z) for z in _upper(12) if _norm(z) == 125}
    assert len(norm125) == 2 > 1


def _real_levels(z: Gauss, degree: int, bound: int) -> list[Poly]:
    """Every ``A = sum_(k=1)^degree a_k z^k`` with ``a_degree != 0``, ``A(z)``
    real and ``|a_k| <= bound`` for ``0 < k < degree``: the top coefficient is
    fixed by the others, as ``Im z^degree != 0``."""
    powers = [(1, 0)]
    for _ in range(degree):
        powers.append(_gmul(powers[-1], z))
    top = powers[degree][1]
    assert top != 0
    out = []
    for low in product(range(-bound, bound + 1), repeat=degree - 1):
        im = sum(a * powers[k + 1][1] for k, a in enumerate(low))
        if im and im % top == 0:
            out.append([0, *low, -im // top])
    return out


def _below_half(n: int) -> int:
    """The largest ``b`` with ``4 b^2 < n``, the bound ``b < sqrt(n)/2``."""
    b = 0
    while 4 * (b + 1) ** 2 < n:
        b += 1
    return b


def test_four_points_of_one_class() -> None:
    """``prop:gaussfour``: at every ``alpha`` off the axes and diagonals with
    ``|alpha|^2 <= 400``, ``|Re alpha^4| >= |alpha|^2`` and no ``A`` of degree
    at most 3 with nonleading coefficients below ``|alpha|/2`` is real at
    ``alpha^4``, and ``A(y^4)`` agrees with it at ``alpha``; ``j = 2|X| - N``
    has ``|j| >= n``; a class meeting the axes or diagonals holds at
    most two points above the axis.

    Control: at the square ``z = beta^2`` of a Pell point ``beta = a + ci``
    (``a^2 - 3c^2 = 1``), not a fourth power, ``z(z - 1)^2`` is real, equal
    to ``-4c^2 (a^2 + c^2)^2``, with coefficients below ``|z|^(1/4)/2`` once
    ``|z| > 256``, and the search of the degree-3 case finds it.
    """
    for alpha in _upper(20):
        a, c = alpha
        n = _norm(alpha)
        if a == 0 or abs(a) == c or n > 400:
            continue
        beta = _gmul(alpha, alpha)
        x, y = _gmul(beta, beta)
        assert y != 0 and abs(x) >= n and x * x + y * y == n**4
        j = 2 * abs(x) - n * n
        assert abs(j) >= n
        for degree in (1, 2, 3):
            assert _real_levels((x, y), degree, _below_half(n)) == []
        h = [0, 0, 0, 0, 5, 0, 0, 0, -2, 0, 0, 0, 1]
        assert _horner(h, alpha) == _horner([0, 5, -2, 1], (x, y))
        cls = _class(alpha)
        assert sum(z[1] > 0 for z in cls) == 4
    for alpha in [(0, 3), (3, 3), (-5, 5), (0, 7)]:
        assert sum(z[1] > 0 for z in _class(alpha)) <= 2
    for a, c in _pell_triples(3):
        z = _gmul((a, c), (a, c))
        big_n = _norm((a, c))
        assert isqrt(big_n) ** 2 != big_n
        assert _horner([0, 1, -2, 1], z) == (-4 * c * c * big_n**2, 0)
        if big_n > 256:
            bound = max(b for b in range(100) if 16 * b**4 < big_n)
            assert bound >= 2
            assert [0, 1, -2, 1] in _real_levels(z, 3, bound)


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
