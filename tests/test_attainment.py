"""Exact checks of ``sec:extremal`` and ``sec:belowtwo`` of the attainment paper.

At roots at least 2 the escaping placement is extremal (``thm:extremal``):
the minimiser for the smaller placement is lifted by one node, directly when
the new zero is aligned (``lem:delete``) and through the run chord
(``prop:runchord``) when it straddles.  Below 2 the conclusion fails
(``prop:belowtwo``); for one exempt coefficient the aligned lift obeys an
exact identity (``thm:halfmass``), which pins the infimum at
``(11/10, 3, 5, 7)`` (``thm:elevenvalue``) and the threshold ``r_c`` along
``(r, 3, 5, 7)`` (``thm:family``); along ``(r, 5, 7)`` it fails for every
``r < 2`` (``prop:cutoffsharp``).

Every tail is exact: a full certificate has used its zero budget, so it keeps
one sign past its largest zero and the rest of its tail is a geometric sum
(``tests/sweep.py``).  Each negative result carries a control, a variant the
same check must catch: the run chord and the deletion step are seen to fail
above the cutoff, and the multiple that beats ``1/tau*`` at
``(11/10, 3, 5, 7)`` has no counterpart at ``(2, 3, 5, 7)``.
"""

from __future__ import annotations

import random
from fractions import Fraction

from tests.sweep import (
    _certificate,
    _partial_sums,
    _simplex_min_t,
    _solve,
    _tail,
    _u,
    min_bk_of,
)

SEED = 20260925


def _tail_of(nodes: list[Fraction], zeros: list[int]) -> Fraction:
    return _tail(nodes, zeros, _certificate(nodes, zeros))


def _roots_to_nodes(roots: list[Fraction]) -> list[Fraction]:
    return [1 / r for r in roots]


def _runs(values: list[int]) -> list[tuple[int, int]]:
    """Maximal runs ``[s, e]`` of consecutive integers of a nonempty set."""
    values = sorted(values)
    out, start, end = [], values[0], values[0]
    for v in values[1:]:
        if v == end + 1:
            end = v
        else:
            out.append((start, end))
            start = end = v
    out.append((start, end))
    return out


def _chord(
    big: Fraction, small: list[Fraction], b0: list[int], g: int, a: list[int]
) -> tuple[Fraction, Fraction]:
    """Both sides of ``eq:runchord``: ``Tail(V)`` and the combination."""
    zeros = sorted(b0 + a)
    tail_f = _tail_of(small, zeros)
    nodes = [big, *small]
    w_zeros = sorted([*b0, g, *(x + 1 for x in a)])
    aw = _certificate(nodes, w_zeros)
    tail_w = _tail(nodes, w_zeros, aw)
    rhos, tails = [], []
    for s, e in _runs(a):
        zj = sorted([z for z in zeros if z != s] + [e + 1])
        aj = _certificate(small, zj)
        tails.append(_tail(small, zj, aj))
        rhos.append(abs(_u(nodes, aw, s)) / abs(_u(small, aj, s)))
    mu = 1 / (1 + sum(rhos))
    # q = sum lambda_j V_j + mu w must vanish on Z, as in the proof.
    for z in zeros:
        q = mu * _u(nodes, aw, z)
        for (s, e), rho in zip(_runs(a), rhos, strict=True):
            zj = sorted([x for x in zeros if x != s] + [e + 1])
            q += mu * rho * _u(small, _certificate(small, zj), z)
        assert q == 0
    rhs = sum(mu * r * t for r, t in zip(rhos, tails, strict=True)) + mu * tail_w
    return tail_f, rhs


def _draw_chord(rng: random.Random, bigs: list[Fraction]):
    while True:
        big = rng.choice(bigs)
        n = rng.randint(2, 4)
        small = sorted(rng.sample([Fraction(1, k) for k in range(3, 12)], n))[::-1]
        if small[0] >= big:
            continue
        g = rng.randint(1, 5)
        nb = rng.randint(0, min(g - 1, n - 2))
        b0 = sorted(rng.sample(range(1, g), nb)) if nb else []
        a = sorted(rng.sample(range(g + 1, g + 8), n - 1 - nb))
        return big, small, b0, g, a


def test_run_chord_below_cutoff() -> None:
    """``prop:runchord`` at a new node ``<= 1/2``, with its equality case."""
    rng = random.Random(SEED)
    bigs = [Fraction(1, 2), Fraction(1, 3)]
    equalities = 0
    for _ in range(150):
        big, small, b0, g, a = _draw_chord(rng, bigs)
        tail_f, rhs = _chord(big, small, b0, g, a)
        tight = big == Fraction(1, 2) and b0 == list(range(1, g))
        assert tail_f >= rhs, (big, small, b0, g, a)
        assert (tail_f == rhs) == tight, (big, small, b0, g, a)
        equalities += tight
    assert equalities >= 5  # the equality case was exercised


def test_run_chord_control_above_cutoff() -> None:
    """The same check fires once the new node exceeds ``1/2``."""
    rng = random.Random(SEED)
    bigs = [Fraction(2, 3), Fraction(3, 4), Fraction(4, 5), Fraction(9, 10)]
    fired = 0
    for _ in range(150):
        tail_f, rhs = _chord(*_draw_chord(rng, bigs))
        fired += tail_f < rhs
    assert fired > 0
    # The instance quoted after prop:runchord.
    small = [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10), Fraction(1, 11)]
    tail_f, rhs = _chord(Fraction(3, 4), small, [1, 2], 3, [7])
    assert tail_f == Fraction(39343118507, 13623090657480)
    assert rhs == Fraction(1246797277705214239223, 416394790925719545961974)
    assert tail_f < rhs


def test_extremal_example_2357() -> None:
    """The example after ``thm:extremal``: ``inf b_2 = 1704/31`` at (2,3,5,7).

    Pins ``tau*`` from both sides, then runs the theorem's covering for every
    placement up to 40: ``{1, 3}`` is lifted by one zero, the straddling
    placement ``2`` through the shifted zero set ``{1, 2, 4}``, which the
    neighbour ``{1, 4}`` licenses.
    """
    tau = Fraction(31, 1704)
    surviving = _roots_to_nodes([Fraction(r) for r in (3, 5, 7)])
    assert _partial_sums([Fraction(r) for r in (3, 5, 7)]) == [1, -14, 57, -48]
    assert _tail_of(surviving, [1, 3]) == tau
    # The weights printed in the paper: v_d = (81 3^-d - 625 5^-d + 686 7^-d)/142.
    assert _certificate(surviving, [1, 3]) == [
        Fraction(81, 142),
        Fraction(-625, 142),
        Fraction(686, 142),
    ]
    sums = _partial_sums([Fraction(r) for r in (3, 5, 7)] + [Fraction(-9, 62)])
    assert max(abs(v) for v in sums[1:]) == 1 / tau
    assert sums[1:] == [
        Fraction(-859, 62),
        Fraction(1704, 31),
        Fraction(-2463, 62),
        Fraction(-1704, 31),
    ]
    # The neighbour of {1, 3} at its only run costs more: F is locally minimal.
    assert _tail_of(surviving, [1, 4]) > tau
    nodes = _roots_to_nodes([Fraction(r) for r in (2, 3, 5, 7)])
    for pos in range(1, 41):
        if pos in (1, 3):
            zeros = [1, 3, 4]
        elif pos == 2:
            zeros = [1, 2, 4]
        else:
            zeros = [1, 3, pos]
        assert pos in zeros
        assert _tail_of(nodes, zeros) <= tau, pos
    # Control: inserting 2 without the shift gives the consecutive set.
    assert _tail_of(nodes, [1, 2, 3]) == Fraction(1, 48) > tau


def _multiply(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def _poly(roots: list[Fraction]) -> list[Fraction]:
    """Ascending coefficients of ``prod (x - r)``."""
    out = [Fraction(1)]
    for r in roots:
        out = _multiply(out, [-r, Fraction(1)])
    return out


def test_below_two() -> None:
    """``prop:belowtwo``: at (11/10, 3, 5, 7) a multiple beats ``1/tau*``."""
    tau = Fraction(31, 1704)
    roots = [Fraction(11, 10), Fraction(3), Fraction(5), Fraction(7)]
    q = [Fraction(5, 12), Fraction(13, 12), Fraction(11, 6), Fraction(5, 2), 1]
    f = _multiply(_poly(roots), [Fraction(c) for c in q])
    assert f == [
        Fraction(385, 8),
        Fraction(293, 6),
        Fraction(997, 20),
        Fraction(823, 20),
        Fraction(-23863, 120),
        Fraction(433, 60),
        Fraction(589, 12),
        Fraction(-68, 5),
        Fraction(1),
    ]
    assert all(sum(c * r**k for k, c in enumerate(f)) == 0 for r in roots)
    b2 = sorted((abs(c) for c in f[:-1]), reverse=True)[1]
    assert b2 == Fraction(997, 20) < 1 / tau
    # The deletion step fails at y_1 = 10/11: lifting {1, 3} by the zero 5.
    nodes = _roots_to_nodes(roots)
    assert _tail_of(nodes, [1, 3, 5]) == Fraction(96935, 3398808) > tau
    # The weights printed in the paper, on (10/11, 1/3, 1/5, 1/7).
    assert _certificate(nodes, [1, 3, 5]) == [
        Fraction(-5153632, 2063784541),
        Fraction(3601989, 5381446),
        Fraction(-17296875, 3682042),
        Fraction(6004901, 1193629),
    ]


def test_below_two_control() -> None:
    """At (2, 3, 5, 7), with the same surviving roots, nothing beats 1704/31.

    The exact linear program over every degree up to 8 and every exempt
    position finds a multiple below 1704/31 at (11/10, 3, 5, 7) and none at
    (2, 3, 5, 7), where ``thm:extremal`` forbids one; and there the lifted
    zero set {1, 3, 5} costs less than ``tau*``, as ``lem:delete`` says.
    """
    tau = Fraction(31, 1704)
    low = min_bk_of(
        _poly([Fraction(11, 10), Fraction(3), Fraction(5), Fraction(7)]), 2, 8
    )
    assert low < 1 / tau
    two = min_bk_of(_poly([Fraction(r) for r in (2, 3, 5, 7)]), 2, 8)
    assert two >= 1 / tau
    nodes = _roots_to_nodes([Fraction(r) for r in (2, 3, 5, 7)])
    assert _tail_of(nodes, [1, 3, 5]) < tau


# --- Below the cutoff: ``sec:belowtwo`` ------------------------------------


def _desc_sums(asc: list[Fraction]) -> list[Fraction]:
    """``S_0, S_1, ...`` of a monic polynomial given by ascending coefficients."""
    out, total = [], Fraction(0)
    for c in reversed(asc):
        total += c
        out.append(total)
    return out


def _exempt_max(asc: list[Fraction], exempt: int) -> Fraction:
    """``max_{j >= 1, j != exempt} |S_j|``; ``S_j`` is constant past the degree."""
    sums = _desc_sums(asc)
    return max(abs(s) for j, s in enumerate(sums) if j >= 1 and j != exempt)


def _correction(nodes: list[Fraction], zstar: list[int]) -> list[Fraction]:
    """``H`` of ``thm:halfmass``: weight 1 on ``nodes[0]``, zero on ``{0} + Z*``."""
    points = [0, *zstar]
    rest = nodes[1:]
    matrix = [[y**d for y in rest] for d in points]
    return [Fraction(1), *_solve(matrix, [-(nodes[0] ** d) for d in points])]


def _mass(nodes: list[Fraction], a: list[Fraction], x: int) -> Fraction:
    return sum((abs(_u(nodes, a, d)) for d in range(1, x + 1)), Fraction(0))


def _beyond(nodes: list[Fraction], a: list[Fraction], x: int) -> Fraction:
    """``sum_{d > x} |u_d|`` for a sum of one sign past ``x``."""
    total = sum(ai * y ** (x + 1) / (1 - y) for ai, y in zip(a, nodes, strict=True))
    return abs(total)


def _half_mass_point(nodes: list[Fraction], zstar: list[int]) -> int:
    """The least ``N > max Z*`` with ``2 sum_{d <= N} |H_d| >= Tail(H)``."""
    h = _correction(nodes, zstar)
    top = max(zstar, default=0)
    whole = _mass(nodes, h, top) + _beyond(nodes, h, top)
    n = top + 1
    while 2 * _mass(nodes, h, n) < whole:
        n += 1
    return n


def _lift_identity(big: Fraction, small: list[Fraction], zstar: list[int], x: int):
    """Both sides of the identity in ``thm:halfmass`` (b)."""
    nodes = [big, *small]
    v = _certificate(small, zstar)
    h = _correction(nodes, zstar)
    c = abs(_u(small, v, x)) / abs(_u(nodes, h, x))
    left = _tail_of(nodes, sorted([*zstar, x]))
    top = max(zstar, default=0)
    tail_v = _tail(small, zstar, v)
    tail_h = _mass(nodes, h, top) + _beyond(nodes, h, top)
    below = _mass(nodes, h, x)
    right = tail_v - 2 * _beyond(small, v, x) - c * (below - (tail_h - below))
    return left, right, tail_v


def test_aligned_lift_identity() -> None:
    """``thm:halfmass`` (b): the aligned lift, at any new node below 1.

    The identity holds for every full ``V`` (minimal or not) and every ``x``
    above its zeros; the control is a straddling ``x``, where it must fail.
    """
    rng = random.Random(SEED)
    bigs = [Fraction(1, 2), Fraction(2, 3), Fraction(3, 4), Fraction(10, 11)]
    straddle_fired = 0
    for _ in range(80):
        big = rng.choice(bigs)
        n = rng.randint(1, 3)
        small = sorted(rng.sample([Fraction(1, k) for k in range(3, 12)], n))[::-1]
        zstar = sorted(rng.sample(range(1, 7), n - 1))
        top = max(zstar, default=0)
        x = rng.randint(top + 1, top + 8)
        left, right, tail_v = _lift_identity(big, small, zstar, x)
        assert left == right, (big, small, zstar, x)
        if x >= _half_mass_point([big, *small], zstar):
            assert left < tail_v
        gaps = [g for g in range(1, top) if g not in zstar]
        if gaps:
            left, right, _ = _lift_identity(big, small, zstar, rng.choice(gaps))
            straddle_fired += left != right
    assert straddle_fired > 0


def test_value_eleven_tenths() -> None:
    """``thm:elevenvalue``: ``inf b_2 = 3398808/96935`` at (11/10, 3, 5, 7).

    Lower: the multiplier ``M`` with position 5 exempt (``lem:exemptpair``).
    Upper: ``thm:halfmass`` with ``N = 11`` and one full certificate per
    remaining placement.  Controls: the window below ``N`` is needed (the
    aligned lift at 9 costs more than ``tau*``) and ``N`` is not smaller.
    """
    tau = Fraction(31, 1704)
    theta = Fraction(96935, 3398808)
    roots = [Fraction(11, 10), Fraction(3), Fraction(5), Fraction(7)]
    nodes = _roots_to_nodes(roots)
    m = [Fraction(69678, 19387), Fraction(52552, 19387), Fraction(1)]
    pm = _multiply(_poly(roots), m)
    assert _desc_sums(pm)[1:] == [
        Fraction(-2401917, 193870),
        1 / theta,
        Fraction(6064861, 193870),
        -1 / theta,
        Fraction(-36840237, 96935),
        1 / theta,
    ]
    assert _exempt_max(pm, 5) == 1 / theta
    assert _tail_of(nodes, [1, 3, 5]) == theta
    assert _half_mass_point(nodes, [1, 3]) == 11
    assert _correction(nodes, [1, 3]) == [
        1,
        Fraction(-14972607, 378004),
        Fraction(11210000, 94501),
        Fraction(-30245397, 378004),
    ]
    witnesses = {2: [1, 2, 10], 4: [1, 4, 9]}
    quoted = [  # the exact tails, and 10**5 * tail floored, as displayed
        (Fraction(843673514383499998315, 40515728086004858188032), 2082),
        (Fraction(29343173972925245, 1145159451474217216), 2562),
        (Fraction(177859285, 8265843096), 2151),
        (Fraction(719323261, 37569613704), 1914),
        (Fraction(181037572242979, 9826348204397256), 1842),
        (Fraction(94783579348745045, 5199121229605850568), 1823),
        (Fraction(199173967015849717825, 10949935864566580087416), 1818),
    ]
    for x, (exact, q) in zip((2, 4, 6, 7, 8, 9, 10), quoted, strict=True):
        zeros = witnesses.get(x, [1, 3, x])
        assert x in zeros
        assert _tail_of(nodes, zeros) == exact, x
        assert exact < theta, x
        assert int(10**5 * exact) == q, x
    assert tau < theta
    # Controls: the aligned lift is above tau* for 4 <= x <= 9 and below at
    # x = 10, and 10 is short of half mass.
    assert _tail_of(nodes, [1, 3, 4]) == Fraction(199, 4200)
    for x in range(4, 10):
        assert _tail_of(nodes, [1, 3, x]) > tau, x
    assert _tail_of(nodes, [1, 3, 10]) < tau
    h = _correction(nodes, [1, 3])
    whole = _mass(nodes, h, 3) + _beyond(nodes, h, 3)
    assert whole == Fraction(2812589, 378004)
    assert 2 * _mass(nodes, h, 10) < whole <= 2 * _mass(nodes, h, 11)
    # Every multiple of degree <= 10 stays above the infimum.
    assert min_bk_of(_poly(roots), 2, 10) >= Fraction(412, 10) > 1 / theta


def _theta(r: Fraction) -> Fraction:
    return (49 * r - 34) / (48 * (r - 1) * (15 * r + 71))


def _family(r: Fraction) -> list[Fraction]:
    return _poly([r, Fraction(3), Fraction(5), Fraction(7)])


# Rational functions of ``r`` over Q, for the closed forms of ``thm:family``.
# Each is kept as a reduced pair of polynomials (ascending ``Fraction``
# coefficients) with a monic denominator, so ``==`` is equality in ``Q(r)``
# and a closed form checked here holds at every ``r``, not at samples.


def _trim(p: list[Fraction]) -> list[Fraction]:
    while p and p[-1] == 0:
        p = p[:-1]
    return p


def _padd(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    n = max(len(p), len(q))
    p, q = p + [Fraction(0)] * (n - len(p)), q + [Fraction(0)] * (n - len(q))
    return _trim([a + b for a, b in zip(p, q, strict=True)])


def _pmul(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    return _trim(_multiply(p, q)) if p and q else []


def _pdivmod(
    p: list[Fraction], q: list[Fraction]
) -> tuple[list[Fraction], list[Fraction]]:
    p, out = list(p), [Fraction(0)] * max(len(p) - len(q) + 1, 1)
    while p and len(p) >= len(q):
        c, k = p[-1] / q[-1], len(p) - len(q)
        out[k] = c
        p = _trim([a - c * q[i - k] if i >= k else a for i, a in enumerate(p)])
    return _trim(out), p


class _Rat:
    """An element of ``Q(r)``; ints and ``Fraction``s coerce to constants."""

    def __init__(self, num: list[Fraction], den: list[Fraction] | None = None):
        num = _trim([Fraction(c) for c in num])
        den = _trim([Fraction(c) for c in den or [1]])
        g, h = num, den
        while h:
            g, h = h, _pdivmod(g, h)[1]
        num, den = _pdivmod(num, g)[0], _pdivmod(den, g)[0]
        self.num = [c / den[-1] for c in num]
        self.den = [c / den[-1] for c in den]

    @staticmethod
    def of(x: _Rat | Fraction | int) -> _Rat:
        return x if isinstance(x, _Rat) else _Rat([Fraction(x)])

    def __add__(self, o: _Rat | Fraction | int) -> _Rat:
        o = _Rat.of(o)
        num = _padd(_pmul(self.num, o.den), _pmul(o.num, self.den))
        return _Rat(num, _pmul(self.den, o.den))

    __radd__ = __add__

    def __neg__(self) -> _Rat:
        return _Rat([-c for c in self.num], self.den)

    def __sub__(self, o: _Rat | Fraction | int) -> _Rat:
        return self + -_Rat.of(o)

    def __rsub__(self, o: Fraction | int) -> _Rat:
        return _Rat.of(o) - self

    def __mul__(self, o: _Rat | Fraction | int) -> _Rat:
        o = _Rat.of(o)
        return _Rat(_pmul(self.num, o.num), _pmul(self.den, o.den))

    __rmul__ = __mul__

    def __truediv__(self, o: _Rat | Fraction | int) -> _Rat:
        o = _Rat.of(o)
        return _Rat(_pmul(self.num, o.den), _pmul(self.den, o.num))

    def __rtruediv__(self, o: Fraction | int) -> _Rat:
        return _Rat.of(o) / self

    def __pow__(self, k: int) -> _Rat:
        out = _Rat([1])
        for _ in range(k):
            out = out * self
        return out

    def __eq__(self, o: object) -> bool:
        if not isinstance(o, _Rat | Fraction | int):
            return NotImplemented
        o = _Rat.of(o)
        return self.num == o.num and self.den == o.den

    __hash__ = None  # type: ignore[assignment]

    def at(self, x: Fraction) -> Fraction:
        value = [Fraction(0), Fraction(0)]
        for i, p in enumerate((self.num, self.den)):
            for c in reversed(p):
                value[i] = value[i] * x + c
        return value[0] / value[1]


def _signed_tail(nodes, zeros: list[int], a) -> _Rat:
    """``Tail`` of a full certificate from the zero bound's sign pattern.

    ``u_0 = 1 > 0`` and ``u`` changes sign exactly at its simple zeros, so
    ``sgn u_d = (-1)^{#{z in Z : z < d}}``; past ``max Z`` the tail is the
    geometric sum ``sum_i a_i y_i^(z+1) / (1 - y_i)`` with that sign.
    """
    top = max(zeros)

    def sign(d: int) -> int:
        return (-1) ** sum(z < d for z in zeros)

    head = sum((sign(d) * _u(nodes, a, d) for d in range(1, top + 1)), _Rat([0]))
    beyond = sum(
        (ai * y ** (top + 1) / (1 - y) for ai, y in zip(a, nodes, strict=True)),
        _Rat([0]),
    )
    return head + sign(top + 1) * beyond


def test_family_threshold() -> None:
    """``thm:family``: at (r, 3, 5, 7), ``T = tau*`` exactly for ``r >= r_c``.

    With ``r`` an indeterminate, the certificates, ``H`` and the partial sums
    are computed over ``Q(r)`` and every closed form the proof uses is checked
    as an identity of rational functions: the tails of the full certificates
    with zero sets {1, 3, 4} and {1, 2, 5}, their differences with ``tau*``,
    ``2 sum_{d<=5} |H_d| - Tail(H)``, the partial sums of ``P_r M`` and the
    quadratics behind ``|S_1|, |S_3| <= beta(r)``.  The signs used are those of
    the zero bound on (1, 3), where ``1/r`` is the largest node; samples
    confirm them against the absolute values.  Control: below ``r_c`` the
    placement 4 beats ``tau*``, and the finite programs never undercut the
    stated infimum.
    """
    tau = Fraction(31, 1704)
    r = _Rat([0, 1])
    nodes = [1 / r, *(_Rat.of(Fraction(1, k)) for k in (3, 5, 7))]
    beta = 48 * (r - 1) * (15 * r + 71) / (49 * r - 34)
    c2 = 214892 * r**3 - 55639 * r**2 - 138630 * r - 266709
    c5 = 206070 * r**3 - 67123 * r**2 - 161312 * r - 238560
    # The two 4x4 systems: tails 1/beta(r) and the quoted quotient.
    t134 = _signed_tail(nodes, [1, 3, 4], _certificate(nodes, [1, 3, 4]))
    t125 = _signed_tail(nodes, [1, 2, 5], _certificate(nodes, [1, 2, 5]))
    denom = 3466 * r**2 + 7455 * r + 11025
    assert t134 == 1 / beta
    assert t125 == (4267 * r**2 + 5070 * r - 5871) / (48 * (r - 1) * denom)
    assert 1 / beta - tau == (1988 + 7 * r - 930 * r**2) / (
        3408 * (r - 1) * (15 * r + 71)
    )
    assert tau - t125 == c2 / (3408 * (r - 1) * denom)
    # The half-mass point: H > 0 past 3 and H_2 < 0, so
    # 2 sum_{d<=5} |H_d| - Tail(H) = -H_2 + H_4 + H_5 - sum_{d>=6} H_d.
    h = _correction(nodes, [1, 3])
    beyond = sum(
        (hi * y**6 / (1 - y) for hi, y in zip(h, nodes, strict=True)), _Rat([0])
    )
    gap = -_u(nodes, h, 2) + _u(nodes, h, 4) + _u(nodes, h, 5) - beyond
    assert gap == c5 * (3 - r) * (5 - r) * (7 - r) / (12524400 * r**5 * (r - 1))
    # The signs used, against the absolute values, at sample points.
    samples = [Fraction(k, 100) for k in range(101, 300, 7)]
    for x in samples:
        points = _roots_to_nodes([x, Fraction(3), Fraction(5), Fraction(7)])
        assert _tail_of(points, [1, 3, 4]) == t134.at(x)
        assert _tail_of(points, [1, 2, 5]) == t125.at(x)
        hx = _correction(points, [1, 3])
        whole = _mass(points, hx, 3) + _beyond(points, hx, 3)
        assert 2 * _mass(points, hx, 5) - whole == gap.at(x)
    # The partial sums of x + m quoted in the proof, at m = 3/2 and at
    # m = (105 - 34 r)/(49 r - 34).
    for mm in (Fraction(3, 2), (105 - 34 * r) / (49 * r - 34)):
        sums = _desc_sums(_multiply(_poly([r, 3, 5, 7]), [mm, _Rat([1])]))
        assert sums[1:4] == [
            mm - r - 14,
            14 * r + 57 - mm * (r + 14),
            mm * (14 * r + 57) - 57 * r - 48,
        ]
        assert sums[5] == 48 * (mm + 1) * (r - 1)
    s1, s2, s3, _, s5 = sums[1:6]
    assert s2 == s5 == beta
    assert s1 == -7 * (7 * r**2 + 98 * r - 83) / (49 * r - 34)
    assert s3 == -(3269 * r**2 + 882 * r - 7617) / (49 * r - 34)
    # |S_1|, |S_3| <= beta: S_1 < 0 there, and the three quadratics.
    assert (beta + s1) * (49 * r - 34) == 671 * r**2 + 2002 * r - 2827
    assert (beta - s3) * (49 * r - 34) == 3989 * r**2 + 3570 * r - 11025
    assert (beta + s3) * (49 * r - 34) == -(2549 * r**2 - 1806 * r - 4209)
    for x in (Fraction(13, 10), Fraction(3, 2)):
        assert s1.at(x) < 0
        assert 671 * x**2 + 2002 * x - 2827 >= 0
        assert 3989 * x**2 + 3570 * x - 11025 >= 0
        assert 2549 * x**2 - 1806 * x - 4209 <= 0
    # The affine partial sums of the fixed multiplier, at both ends of (1, 13/10].
    ends = {
        Fraction(1): [Fraction(-27, 2), Fraction(97, 2), Fraction(3, 2), 0],
        Fraction(13, 10): [Fraction(-69, 5), Fraction(209, 4), Fraction(-93, 10), 36],
    }
    for x, quoted in ends.items():
        mult = [Fraction(3, 2), Fraction(1)]
        sums = _desc_sums(_multiply(_family(x), mult))
        assert [sums[1], sums[2], sums[3], sums[5]] == quoted
        assert _exempt_max(_multiply(_family(x), mult), 4) <= Fraction(209, 4)
        assert Fraction(209, 4) < 1 / tau
    # r_c, and the cubics: positive at 29/20 with derivatives positive on r >= 1.
    rc_poly = 930 * r**2 - 7 * r - 1988
    assert rc_poly.at(Fraction(1465, 1000)) < 0 < rc_poly.at(Fraction(1466, 1000))
    x = Fraction(29, 20)
    assert c2.at(x) > 0 and c5.at(x) > 0
    assert 644676 - 111278 - 138630 > 0 and 618210 - 134246 - 161312 > 0
    # Control: at r = 29/20 < r_c the placement 4 is worst, above tau*, and
    # the finite programs stay above 1/theta.
    assert _theta(x) > tau
    assert min_bk_of(_family(x), 2, 8) > 1 / _theta(x)
    # At r = 3/2 the escaping placement is extremal: inf b_2 = 1704/31.
    assert _theta(Fraction(3, 2)) < tau


def test_cutoff_sharp() -> None:
    """``prop:cutoffsharp``: at (r, 5, 7), ``T > tau* = 1/24`` for every r < 2.

    Control: at r = 2 the same multiplier gives exactly 24, and no multiple
    of small degree goes below 24, as ``thm:extremal`` requires.
    """
    nodes = [Fraction(1, 5), Fraction(1, 7)]
    assert _tail_of(nodes, [1]) == Fraction(1, 24)
    assert max(abs(s) for s in _partial_sums([Fraction(5), Fraction(7)])[1:]) == 24
    for k in range(101, 200):
        r = Fraction(k, 100)
        p = _poly([r, Fraction(5), Fraction(7)])
        assert _desc_sums(p)[1:] == [-(r + 11), 11 * r + 24, -24 * (r - 1)]
        assert _exempt_max(p, 2) == max(r + 11, 24 * (r - 1)) < 24
    two = _poly([Fraction(2), Fraction(5), Fraction(7)])
    assert _exempt_max(two, 2) == 24
    assert min_bk_of(two, 2, 7) >= 24


def _min_b2_exempting(poly: list[Fraction], degree: int, exempt: int) -> Fraction:
    """Exact ``min b_2`` over monic multiples of ``poly`` of the given degree
    whose largest nonleading coefficient sits at position ``exempt``."""
    deg_p = len(poly) - 1
    n = degree - deg_p
    keep = [j for j in range(degree) if j != exempt]
    rows = [
        [poly[j - i] if 0 <= j - i <= deg_p else Fraction(0) for i in range(n)]
        for j in keep
    ]
    const = [poly[j - n] if 0 <= j - n <= deg_p else Fraction(0) for j in keep]
    return _simplex_min_t(rows, const)


def test_infimum_approached_directly() -> None:
    """``inf b_2 = 1704/31`` at ``(2,3,5,7)``, checked by optimizing over
    multiples rather than by replaying the certificate: the exact optimum at
    each degree up to 30 stays above ``1704/31`` and comes within ``1/1000``
    of it, and at degree 14 the best exempt position is the constant term,
    the escaping placement of ``thm:extremal``.

    Control: the row value ``48`` of ``thm:order`` at ``u = 1`` is not the
    infimum here, as the partial-sum criterion fails.
    """
    poly = _poly([Fraction(r) for r in (2, 3, 5, 7)])
    target = Fraction(1704, 31)
    values = [_min_b2_exempting(poly, d, 0) for d in (10, 15, 20, 25, 30)]
    assert all(a > b > target for a, b in zip(values, values[1:], strict=False))
    assert values[-1] - target < Fraction(1, 1000)
    at14 = [_min_b2_exempting(poly, 14, e) for e in range(14)]
    assert min(at14) == at14[0]
    assert min(at14) > target > 48
