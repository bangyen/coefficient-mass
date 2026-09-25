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


# Several annuli (lem:central, lem:tropcount, thm:annuli, cor:annuli,
# prop:annulisharp).


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


def test_count_at_a_distance() -> None:
    """``lem:tropcount``: ``n`` zeros of modulus ``>= R`` put every central index
    at ``r < R/9^n`` at least ``n`` below the top."""
    rng = random.Random(SEED + 12)
    for _ in range(200):
        pairs = [rng.choice(PYTHAGOREAN) for _ in range(rng.randint(1, 3))]
        f = _mul(_product([_pair(a, b) for a, b, _ in pairs]), _cofactor(rng))
        n = 2 * len(pairs)
        r = Fraction(min(rho for *_, rho in pairs), 9**n + 1)
        assert all(len(f) - 1 - y >= n for y in _central(f, r))


def test_count_needs_distance() -> None:
    """The control: at a constant distance the count fails.  ``(x - 10)^12`` has
    ``12`` zeros of modulus ``10`` but a positive central index at ``10/11``."""
    f = _product([[-10, 1]] * 12)
    assert all(len(f) - 1 - y < 12 for y in _central(f, Fraction(10, 11)))
    assert all(len(f) - 1 - y >= 12 for y in _central(f, Fraction(10, 9**12 + 1)))


def _annuli(rng: random.Random, gap: int) -> list[list[tuple[int, int, int]]]:
    """Pairs in ``S`` annuli, ``T_a`` above ``(3 U_(a-1) + 1) 9^(n_a)`` if
    ``gap == 0`` (so ``r_a = 3 U_(a-1) + 1`` has ``k_a = n_a``), else above
    ``gap * U_(a-1)``."""
    small = [p for p in PYTHAGOREAN if p[2] >= 5]
    annuli = [[rng.choice(small) for _ in range(rng.randint(1, 2))]]
    for _ in range(rng.randint(1, 2)):
        annuli.append([rng.choice(small)])
    for a in range(1, len(annuli)):
        n_a = 2 * sum(len(ann) for ann in annuli[a:])
        upper = max(p[2] for p in annuli[a - 1])
        need = (3 * upper + 1) * 9**n_a if gap == 0 else gap * upper
        c = need // 5 + 1  # scale (3, 4, 5)-type pairs past ``need``
        annuli[a] = [(c * x, c * y, c * rho) for x, y, rho in annuli[a]]
        assert min(p[2] for p in annuli[a]) > need
    return annuli


def test_annuli_exact_counts() -> None:
    """``thm:annuli`` with ``k_a = n_a`` and ``cor:annuli`` item 1: positions,
    counts, values, rows and mass, at separation ``3 * 9^(n_a)``."""
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
            kappa = max(k for k in range(64) if 9**k < low / r)
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


def _lacunary(ns: list[int], ts: list[int]) -> Poly:
    """``prop:annulisharp`` item 1: ``sum_a c_a x^(y_a)``."""
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
