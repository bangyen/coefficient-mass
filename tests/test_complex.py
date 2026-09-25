"""Exact checks of ``coefficient-mass-complex.tex``.

Each bound is checked on seeded random integer multiples, where every
coefficient is exact; roots of irrational modulus are avoided by using
Pythagorean Gaussian integers.  Every group has a control that a false
variant of its statement is caught.
"""

from __future__ import annotations

import random
from fractions import Fraction
from math import ceil, prod

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


# Wide sectors (prop:widesharp).


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
