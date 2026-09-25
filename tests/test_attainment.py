"""Exact checks of ``sec:extremal`` and ``sec:belowtwo`` of the attainment paper.

At roots at least 2 the escaping placement is extremal (``thm:extremal``):
the minimiser for the smaller placement is lifted by one node, directly when
the new zero is aligned (``lem:delete``) and through the run chord
(``prop:runchord``) when it straddles.  Below 2 the conclusion fails
(``prop:belowtwo``); for one exempt coefficient the aligned lift obeys an
exact identity (``thm:halfmass``), which pins the infimum at
``(11/10, 3, 5, 7)`` (``thm:elevenvalue``), the threshold ``r_c`` along
``(r, 3, 5, 7)`` (``thm:family``) and the infimum there in seven pieces down
to ``r = 1.0745...`` (``thm:familylow``, signs on intervals by Sturm counts),
and ``inf b_2 - 24`` of order ``(r - 1)^alpha`` as ``r -> 1`` (``lem:threenode``,
``thm:familyone``), with an oscillating constant (``lem:eighteen``,
``thm:familyosc``, ``prop:familyrdelta``); every cost along the family is
explicit (``thm:familyzero``), with a limit profile (``thm:familylimit``) that
decides the jumps (``thm:familyjump``); along ``(r, 5, 7)`` it fails for every
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


def _window_roots(x: Fraction) -> list[Fraction]:
    return [x, Fraction(3), Fraction(5), Fraction(7)]


def test_family_window() -> None:
    """``thm:family`` on ``[13/10, 29/20)``: ``inf b_2 = beta(r)`` there too.

    Over ``Q(r)``: the half-mass point is at most 6 (``c_6``), and the full
    certificates with zero sets {1, 2, 5} and {1, 3, 5} cost less than
    ``1/beta(r)`` (``d_2``, ``d_5``), so by ``thm:halfmass`` only the placement
    4 reaches ``1/beta(r)``.  The weights of {1, 3, 5}, ``H_6`` and the sum of
    ``H`` past 6 are the closed forms of ``sec:familydata``.  Controls: at
    ``r = 5/4`` the half-mass point is 7 and the multiplier of the lower bound
    exceeds ``beta``, so the argument stops short of 13/10 for both reasons.
    """
    tau = Fraction(31, 1704)
    r = _Rat([0, 1])
    nodes = [1 / r, *(_Rat.of(Fraction(1, k)) for k in (3, 5, 7))]
    beta = 48 * (r - 1) * (15 * r + 71) / (49 * r - 34)
    p = (3 - r) * (5 - r) * (7 - r)
    q = 3466 * r**2 + 7455 * r + 11025
    q5 = 960 * r**2 + 5041 * r + 7455
    c6 = 23062470 * r**4 - 598283 * r**3 - 7874752 * r**2 - 16937760 * r - 25048800
    d2 = 105829 * r**3 - 131556 * r**2 + 14850 * r + 41991
    d5 = -1670 * r**3 - 23167 * r**2 + 30517 * r + 34080
    # The certificate {1, 3, 5}: weights, values and tail.
    a = _certificate(nodes, [1, 3, 5])
    assert a == [
        -960 * r**5 / (p * q5),
        729 * (r + 5) * (r + 7) / (2 * (3 - r) * q5),
        -15625 * (r + 3) * (r + 7) / (2 * (5 - r) * q5),
        16807 * (r + 3) * (r + 5) / ((7 - r) * q5),
    ]
    assert [_u(nodes, a, d) for d in range(6)] == [
        1,
        0,
        -(71 * r + 105) / q5,
        0,
        (r + 15) / q5,
        0,
    ]
    past = sum((ai * y**6 / (1 - y) for ai, y in zip(a, nodes, strict=True)), _Rat([0]))
    assert past == -(7 * r**2 + 98 * r + 375) / (24 * (r - 1) * q5)
    t135 = _signed_tail(nodes, [1, 3, 5], a)
    t125 = _signed_tail(nodes, [1, 2, 5], _certificate(nodes, [1, 2, 5]))
    assert t135 == 5 * (347 * r**2 + 250 * r - 501) / (24 * (r - 1) * q5)
    assert 1 / beta - t125 == d2 / (48 * (r - 1) * (15 * r + 71) * q)
    assert 1 / beta - t135 == d5 / (16 * (r - 1) * (15 * r + 71) * q5)
    # The half-mass point: 2 sum_{d<=6} |H_d| - Tail(H), from H_2 < 0 < H_d (d > 3).
    h = _correction(nodes, [1, 3])
    h6 = _u(nodes, h, 6)
    beyond = sum(
        (hi * y**7 / (1 - y) for hi, y in zip(h, nodes, strict=True)), _Rat([0])
    )
    assert h6 == p * (44535 * r**3 + 246086 * r**2 + 529305 * r + 782775) / (
        82191375 * r**6
    )
    assert beyond == p * (
        430890 * r**4 + 2035579 * r**3 + 3937376 * r**2 + 8468880 * r + 12524400
    ) / (1315062000 * r**6 * (r - 1))
    gap = -_u(nodes, h, 2) + _u(nodes, h, 4) + _u(nodes, h, 5) + h6 - beyond
    assert gap == c6 * p / (1315062000 * r**6 * (r - 1))
    # Signs: c_6 and d_2 increase on r >= 1, d_5 decreases, via the bounds
    # quoted in the proof, and the end values.
    assert 92249880 - 1794849 - 15749504 - 16937760 == 57767767
    assert 317487 - 263112 == 54375
    assert -5010 - 46334 + 30517 < 0
    assert c6.at(Fraction(13, 10)) == Fraction(522259242, 125) > 0
    # c_2 and c_5 of test_family_threshold are negative at 13/10: the window
    # needs the extra term of H and the certificate bound 1/beta, not tau*.
    x = Fraction(13, 10)
    assert 214892 * x**3 - 55639 * x**2 - 138630 * x - 266709 < 0
    assert 206070 * x**3 - 67123 * x**2 - 161312 * x - 238560 < 0
    assert d2.at(Fraction(1)) == 31114
    assert d5.at(Fraction(3, 2)) == Fraction(44187, 2)
    # The same facts at sample points of the window, against absolute values.
    for k in range(130, 145):
        x = Fraction(k, 100)
        points = _roots_to_nodes(_window_roots(x))
        assert _tail_of(points, [1, 3, 5]) == t135.at(x) < _theta(x)
        assert _tail_of(points, [1, 2, 5]) == t125.at(x) < _theta(x)
        assert _tail_of(points, [1, 3, 4]) == _theta(x) > tau
        assert _half_mass_point(points, [1, 3]) <= 6
    # Controls: the multiples of small degree stay above beta at 13/10, and at
    # 5/4 both the half-mass bound and the lower-bound multiplier fail.
    x = Fraction(13, 10)
    assert min_bk_of(_family(x), 2, 8) > 1 / _theta(x)
    x = Fraction(5, 4)
    assert c6.at(x) < 0
    assert _half_mass_point(_roots_to_nodes(_window_roots(x)), [1, 3]) == 7
    mult = [(105 - 34 * x) / (49 * x - 34), Fraction(1)]
    assert _exempt_max(_multiply(_family(x), mult), 4) > 1 / _theta(x)


# --- The family below 13/10: ``thm:familylow`` -------------------------------


def _peval(p: list[Fraction], x: Fraction) -> Fraction:
    value = Fraction(0)
    for c in reversed(p):
        value = value * x + c
    return value


def _sturm(p: list[Fraction], a: Fraction, b: Fraction) -> int:
    """Distinct real zeros of ``p`` in ``(a, b]``, by Sturm's theorem.

    The count is exact over Q; ``p`` must not vanish at ``a`` or ``b``.
    """
    assert _peval(p, a) != 0 and _peval(p, b) != 0
    chain = [p, _trim([i * c for i, c in enumerate(p)][1:])]
    while len(chain[-1]) > 1:
        rem = _pdivmod(chain[-2], chain[-1])[1]
        if not rem:
            break
        chain.append([-c for c in rem])

    def changes(x: Fraction) -> int:
        signs = [v > 0 for v in (_peval(q, x) for q in chain) if v != 0]
        return sum(s != t for s, t in zip(signs, signs[1:], strict=False))

    return changes(a) - changes(b)


def _positive_on(f: _Rat, a: Fraction, b: Fraction) -> bool:
    """``f > 0`` on ``[a, b]``: numerator and denominator have no zero there
    (Sturm), and ``f(a) > 0``."""
    for p in (f.num, f.den):
        if _peval(p, a) == 0 or _peval(p, b) == 0 or _sturm(p, a, b):
            return False
    return f.at(a) > 0


def _witness(nodes, zeros: list[int]) -> tuple[dict[int, _Rat], _Rat]:
    """The multiplier witness of a full certificate with zero set ``Z``.

    Off ``Z`` put ``s_d = sgn u_d = (-1)^{#{z in Z : z < d}}``; on ``Z`` the
    ``s_d``, and ``theta``, solve ``sum_{d >= 1} s_d y^d = theta`` at every
    node, the part past ``max Z`` a geometric sum.  Then ``w_0 = 1``,
    ``w_d = -s_d/theta`` is bounded and its series vanishes at every node.
    """
    top = max(zeros)

    def sign(d: int) -> int:
        return (-1) ** sum(z < d for z in zeros)

    matrix, rhs = [], []
    for y in nodes:
        matrix.append([y**d for d in zeros] + [_Rat([-1])])
        known = sum(
            (sign(d) * y**d for d in range(1, top + 1) if d not in zeros), _Rat([0])
        )
        rhs.append(-(known + sign(top + 1) * y ** (top + 1) / (1 - y)))
    sol = _solve(matrix, rhs)
    return dict(zip(zeros, sol[:-1], strict=True)), sol[-1]


def _half_gap(nodes, n: int) -> _Rat:
    """``2 sum_{d<=n} |H_d| - Tail(H)`` from ``H_2 < 0 < H_d`` (``d > 3``)."""
    h = _correction(nodes, [1, 3])
    head = -_u(nodes, h, 2) + sum((_u(nodes, h, d) for d in range(4, n + 1)), _Rat([0]))
    beyond = sum(
        (hi * y ** (n + 1) / (1 - y) for hi, y in zip(h, nodes, strict=True)),
        _Rat([0]),
    )
    return head - beyond


def _rpoly(coeffs: list[int]) -> _Rat:
    """The polynomial with the given coefficients, highest degree first."""
    return _Rat([Fraction(c) for c in reversed(coeffs)])


#: The breakpoint polynomials ``gamma`` of ``thm:familylow`` (keys: their
#: indices, and ``gamma'``, ``gamma_+``), highest degree first, each with one
#: zero in (1, 3/2), bracketed between the two numbers over 10000.
_BREAKS = {
    1: ([218644, 418845, 374850, -1157625], (10740, 10750)),
    2: ([203860, 341469, 134274, -824889], (10950, 10960)),
    "prime": (
        [
            172587443623,
            203696380262,
            -245023502843,
            -16113960832,
            -40364204160,
            -86819140800,
            -128394504000,
        ],
        (11110, 11120),
    ),
    3: (
        [
            31863386060,
            527299949544,
            2216976743064,
            5148085143336,
            7473795889089,
            2333772047565,
            -9236198868099,
            -16544067678495,
        ],
        (11244, 11245),
    ),
    4: (
        [
            1638534863,
            1910488822,
            -2452391683,
            -384420992,
            -826848960,
            -1222804800,
        ],
        (11330, 11340),
    ),
    5: ([15476503, 17470982, -26164523, -7874752, -11645760], (11660, 11670)),
    6: ([144543, 150742, -305683, -110912], (12150, 12160)),
    7: ([3989, 3570, -11025], (12740, 12750)),
    "plus": ([111700, -50307, -97470, -109209], (14830, 14840)),
}

#: ``Q_z`` in the denominators for the zero sets {1, 4, z}.
_QS = {
    5: [77, 480, 1733],
    6: [9359, 60705, 246086, 363930],
    7: [421939, 2798055, 12013156, 25839030, 38212650],
    8: [8457547, 56817765, 251780638, 630690690, 1356549075, 2006164125],
}

#: Numerators of the tails ``theta_z`` of {1, 4, z}, and the constants ``k``
#: with ``theta_z = numerator / (k (r - 1) Q_z)``.
_THETAS = {
    5: ([769, 3374, -3989], 96),
    6: ([49550, 244468, 148970, -433629], 48),
    7: ([2308315, 12063338, 17059705, 15420090, -46429509], 48),
    8: (
        [94332044, 508724104, 933286436, 1788992289, 1607184810, -4915604589],
        96,
    ),
}


def test_family_below() -> None:
    """``thm:familylow``: the infimum along (r, 3, 5, 7) on ``[rho_1, 13/10]``.

    Over ``Q(r)``: the tails ``theta_z`` of the full certificates {1, 4, z}
    and their multiplier witnesses, whose entries on the zero set lie in
    ``[-1, 1]`` exactly between consecutive breakpoints; the witnesses for
    placement 5 at {1, 3, 5} and {1, 4, 5}; the crossing ``rho_3`` of placements
    4 and 5; ``N <= 13``, with ``N <= x`` past ``b_x``; and one certificate
    per remaining placement cheaper than ``T``.  Every sign on an interval is
    a Sturm count over Q.  Controls: each witness fails outside its piece,
    ``N`` is 13 and not 12 at ``rho_1``, and the finite programs stay above
    ``1/T``.
    """
    tau = Fraction(31, 1704)
    r = _Rat([0, 1])
    nodes = [1 / r, *(_Rat.of(Fraction(1, k)) for k in (3, 5, 7))]
    lo, hi = Fraction(1), Fraction(3, 2)
    g = {key: _rpoly(c) for key, (c, _) in _BREAKS.items()}
    # Each breakpoint polynomial: one zero in (1, 3/2), from - to +, bracketed.
    brackets = {}
    for key, (_, (a, b)) in _BREAKS.items():
        a, b = Fraction(a, 10000), Fraction(b, 10000)
        assert _sturm(g[key].num, lo, hi) == 1, key
        assert g[key].at(lo) < 0 < g[key].at(hi), key
        assert g[key].at(a) < 0 < g[key].at(b), key
        brackets[key] = (a, b)
    order = [1, 2, "prime", 3, 4, 5, 6, 7]
    assert all(
        brackets[s][1] <= brackets[t][0] for s, t in zip(order, order[1:], strict=False)
    )
    r1 = brackets[1][0]  # a rational just below rho_1
    top = Fraction(13, 10)
    assert brackets[7][1] < top < brackets["plus"][0]

    def tail(zeros: list[int]) -> _Rat:
        return _signed_tail(nodes, zeros, _certificate(nodes, zeros))

    q5 = 960 * r**2 + 5041 * r + 7455
    t5 = tail([1, 3, 5])
    assert t5 == 5 * (347 * r**2 + 250 * r - 501) / (24 * (r - 1) * q5)
    theta = {3: tail([1, 3, 4])}
    assert theta[3] == (49 * r - 34) / (48 * (r - 1) * (15 * r + 71))
    qs = {z: _rpoly(c) for z, c in _QS.items()}
    for z, (c, k) in _THETAS.items():
        theta[z] = tail([1, 4, z])
        assert theta[z] == _rpoly(c) / (k * (r - 1) * qs[z]), z
    # The ties: consecutive tails agree exactly at the breakpoints.
    assert theta[3] - theta[5] == -(r + 15) * g[7] / (
        96 * (r - 1) * (15 * r + 71) * qs[5]
    )
    assert t5 - theta[5] == -(r + 15) * g[2] / (96 * (r - 1) * qs[5] * q5)
    assert t5 - theta[8] == -g[3] / (96 * (r - 1) * q5 * qs[8])
    assert theta[5] - theta[6] == -(r**2 + 15 * r + 154) * g[6] / (
        32 * (r - 1) * qs[5] * qs[6]
    )
    assert theta[6] - theta[7] == -(15 * r**3 + 225 * r**2 + 2310 * r + 9359) * g[5] / (
        16 * (r - 1) * qs[6] * qs[7]
    )
    assert theta[7] - theta[8] == -7 * (
        22 * r**4 + 330 * r**3 + 3388 * r**2 + 17745 * r + 60277
    ) * g[4] / (32 * (r - 1) * qs[7] * qs[8])
    # The certificate {1, 4, 5} and its witness, as in sec:familydata.
    p = (3 - r) * (5 - r) * (7 - r)
    q = qs[5]
    a = _certificate(nodes, [1, 4, 5])
    assert a == [
        -77 * r**5 / (p * q),
        243 * (r**2 + 12 * r + 109) / (16 * (3 - r) * q),
        -3125 * (r**2 + 10 * r + 79) / (8 * (5 - r) * q),
        16807 * (r**2 + 8 * r + 49) / (16 * (7 - r) * q),
    ]
    assert [_u(nodes, a, d) for d in range(6)] == [
        1,
        0,
        -(15 * r + 71) / (2 * q),
        -(r + 15) / (2 * q),
        0,
        0,
    ]
    past = sum((ai * y**6 / (1 - y) for ai, y in zip(a, nodes, strict=True)), _Rat([0]))
    assert past == -(r**2 + 14 * r + 139) / (96 * (r - 1) * q)
    s = _witness(nodes, [1, 4, 5])[0]
    assert s[1] == (769 * r**3 + 10766 * r**2 + 42091 * r - 52276) / (96 * (r - 1) * q)
    assert s[4] == (211252 * r**3 + 380157 * r**2 + 254562 * r - 991257) / (
        96 * (r - 1) * q
    )
    assert s[5] == -(142079 * r**3 + 137846 * r**2 - 345779 * r - 55456) / (
        32 * (r - 1) * q
    )
    # rho_7 = (105 sqrt(4278) - 1785)/3989, the zero of gamma_7.
    assert 3570**2 + 4 * 3989 * 11025 == 210**2 * 4278
    # Lower bounds: the witnesses, piece by piece.  ``(1 - s_c) den`` and
    # ``(1 + s_c) den`` are the displayed multiples of breakpoint polynomials.
    pieces = [  # placement, zero set, checked entry c, den, 1 - s_c, 1 + s_c
        (
            4,
            [1, 3, 4],
            3,
            48 * (r - 1) * (15 * r + 71),
            -(2549 * r**2 - 1806 * r - 4209),
            g[7],
        ),
        (4, [1, 4, 5], 5, 32 * (r - 1) * qs[5], g[6], -35 * r * g[7]),
        (4, [1, 4, 6], 6, 16 * (r - 1) * qs[6], g[5], -105 * r * g[6]),
        (4, [1, 4, 7], 7, 16 * (r - 1) * qs[7], g[4], -105 * r * g[5]),
        (4, [1, 4, 8], 8, 32 * (r - 1) * qs[8], g["prime"], -105 * r * g[4]),
        (5, [1, 3, 5], 3, 48 * (r - 1) * q5, -g["plus"], g[2]),
        (5, [1, 4, 5], 4, 96 * (r - 1) * qs[5], -g[2], g[1]),
    ]
    for x, zeros, c, den, minus, plus in pieces:
        s, th = _witness(nodes, zeros)
        assert th == tail(zeros), zeros
        for y in nodes:  # the series of w vanishes at every node
            assert (
                sum((s[d] * y**d for d in zeros), _Rat([0]))
                + sum(
                    (
                        (-1) ** sum(z < d for z in zeros) * y**d
                        for d in range(1, max(zeros) + 1)
                        if d not in zeros
                    ),
                    _Rat([0]),
                )
                + (-1) ** len(zeros) * y ** (max(zeros) + 1) / (1 - y)
                == th
            )
        assert (1 - s[c]) * den == minus, zeros
        assert (1 + s[c]) * den == plus, zeros
        assert _positive_on(den, r1, hi)
        # |s_1| < 1 on the whole range; the placement's own entry is free.
        assert _positive_on(1 - s[1], r1, hi) and _positive_on(1 + s[1], r1, hi)
        assert x in zeros and x != c
    # 1 - s_3 at {1, 3, 4}: concave, positive at both ends of [1, 3/2].
    assert _positive_on(4209 + 1806 * r - 2549 * r**2, lo, hi)
    # Inside each piece the checked entry lies in [-1, 1].
    inside = [Fraction(129, 100), Fraction(5, 4), Fraction(6, 5), Fraction(23, 20)]
    inside += [Fraction(28, 25), Fraction(11, 10), Fraction(27, 25)]
    for (_, zeros, c, *_), x in zip(pieces, inside, strict=True):
        assert abs(_witness(nodes, zeros)[0][c].at(x)) <= 1, zeros
    # Control: each witness fails just outside its piece.
    s6 = _witness(nodes, [1, 4, 6])[0][6]
    assert s6.at(Fraction(5, 4)) < -1 and s6.at(Fraction(23, 20)) > 1
    s4 = _witness(nodes, [1, 4, 5])[0][4]
    assert s4.at(Fraction(107, 100)) < -1 and s4.at(Fraction(11, 10)) > 1
    # Placement 4 below rho_3, placement 5 above: theta_8 < min(t_5, theta_5)
    # on [rho_1, rho_3), and t_5 < theta_z (z = 3, 5, 6, 7) past 1.1242 < rho_3.
    assert _positive_on(theta[5] - theta[8], r1, Fraction(118, 100))
    cut = Fraction(11242, 10000)
    assert brackets[4][0] > brackets[3][0] >= cut
    for z in (3, 5, 6, 7):
        assert _positive_on(theta[z] - t5, cut, top), z
    # Control: the Sturm check sees the crossing at rho_3 from either side.
    assert not _positive_on(t5 - theta[8], r1, top)
    assert not _positive_on(theta[8] - t5, r1, top)
    # tau* < min(t_5, theta_5), so the placements 1 and 3 cost less than T.
    assert _positive_on(t5 - tau, r1, top) and _positive_on(theta[5] - tau, r1, top)
    # The half-mass point: N <= 13 on [rho_1, 13/10], N <= x past b_x.
    ends = {
        13: r1,
        12: Fraction(1081, 1000),
        11: Fraction(1092, 1000),
        10: Fraction(1106, 1000),
        9: Fraction(1125, 1000),
        8: Fraction(1153, 1000),
        7: Fraction(1197, 1000),
        6: Fraction(1274, 1000),
    }
    for n, b in ends.items():
        assert _positive_on(_half_gap(nodes, n), b, top), n
    # Upper bounds: the aligned lift {1, 3, x} for 6 <= x <= 12 below b_x,
    # {1, 2, 13} and {1, 2, 10} for placement 2.
    for x in range(6, 13):
        t = tail([1, 3, x])
        assert _positive_on(t5 - t, r1, ends[x]), x
        assert _positive_on(theta[5] - t, r1, ends[x]), x
    split = Fraction(1112, 1000)
    assert brackets["prime"][1] <= split
    t = tail([1, 2, 13])
    assert _positive_on(t5 - t, r1, split) and _positive_on(theta[5] - t, r1, split)
    t = tail([1, 2, 10])
    for z in (3, 5, 6, 7, 8):
        assert _positive_on(theta[z] - t, split, top), z
    # At 11/10 the value is that of thm:elevenvalue.
    assert t5.at(Fraction(11, 10)) == Fraction(96935, 3398808)
    assert 1 / theta[5].at(Fraction(5, 4)) == Fraction(314024, 7627)
    # Controls: N is 13 at rho_1, not 12; below rho_2 the certificate {1, 3, 5}
    # is not the cheapest for placement 5; the finite programs stay above 1/T.
    points = _roots_to_nodes(_window_roots(r1))
    assert _half_mass_point(points, [1, 3]) == 13
    assert _half_gap(nodes, 12).at(r1) < 0
    assert t5.at(Fraction(108, 100)) > theta[5].at(Fraction(108, 100))
    for x, value in ((Fraction(6, 5), theta[6]), (Fraction(9, 8), theta[8])):
        assert min_bk_of(_family(x), 2, 8) > 1 / value.at(x)


# --- The family near r = 1: ``thm:familyone`` --------------------------------

_FAST = [Fraction(1, 3), Fraction(1, 5), Fraction(1, 7)]


def _three_node(a3, b5, c7):
    """``lem:threenode`` at ``A = 3^-x``, ``B = 5^-x``, ``C = 7^-x``.

    The weights of the full certificate {1, x} on (1/3, 1/5, 1/7), its tail
    ``t`` and the witness entries ``s_1``, ``s_x``, as rational functions of
    ``A``, ``B``, ``C``.
    """
    d = 3 * a3 - 10 * b5 + 7 * c7
    lam = [
        3 * (5 * b5 - 7 * c7) / (2 * d),
        -5 * (3 * a3 - 7 * c7) / (2 * d),
        7 * (3 * a3 - 5 * b5) / (2 * d),
    ]
    t = (3 * a3 - 20 * b5 + 21 * c7 + 90 * a3 * b5 - 168 * a3 * c7 + 70 * b5 * c7) / (
        24 * d
    )
    s1 = (
        11 * a3 - 60 * b5 + 49 * c7 + 210 * a3 * b5 - 280 * a3 * c7 + 70 * b5 * c7
    ) / (8 * d)
    sx = (1 - 36 * a3 + 90 * b5 - 56 * c7) / (6 * d)
    return lam, t, s1, sx


def _at_x(x: int):
    return _three_node(Fraction(1, 3**x), Fraction(1, 5**x), Fraction(1, 7**x))


def _pattern(y, x: int, s1, sx, flip: tuple[int, Fraction] | None = None):
    """``sum_{d >= 1} rho_d y^d`` for the witness pattern of ``lem:threenode``
    (``s_1``, then -1 up to ``x``, ``s_x``, then +1), flipped to -1 past ``z``
    with value ``1 - 2 phi`` at ``z`` when ``flip = (z, phi)``."""
    total = s1 * y - (y**2 - y**x) / (1 - y) + sx * y**x
    if flip is None:
        return total + y ** (x + 1) / (1 - y)
    z, phi = flip
    total += (y ** (x + 1) - y**z) / (1 - y)
    return total + (1 - 2 * phi) * y**z - y ** (z + 1) / (1 - y)


def _flip_correction(z: int, phi: Fraction) -> list[Fraction]:
    """``c_1, c_2, c_3`` with ``sum_j c_j a^j = delta(a)`` at the fast nodes."""
    delta = [2 * phi * a**z + 2 * a ** (z + 1) / (1 - a) for a in _FAST]
    return _solve([[a, a**2, a**3] for a in _FAST], delta)


def _flip_witness(r: Fraction, x: int):
    """The witness of ``thm:familyone`` for the placement ``x``: the flip point
    ``(z, phi)`` with ``z >= x + 3`` and the correction ``c``, found by walking
    the flip outwards until ``F`` changes sign (``F`` is affine in ``phi``)."""
    y = 1 / r
    _, t, s1, sx = _at_x(x)

    def big_f(z: int, phi: Fraction) -> Fraction:
        c = _flip_correction(z, phi)
        head = sum(cj * y ** (j + 1) for j, cj in enumerate(c))
        return _pattern(y, x, s1, sx, (z, phi)) + head - t

    z = x + 3
    if big_f(z, Fraction(1)) >= 0:
        return None
    while big_f(z, Fraction(0)) < 0:
        z += 1
    f1, f0 = big_f(z, Fraction(1)), big_f(z, Fraction(0))
    phi = f0 / (f0 - f1)
    assert 0 <= phi <= 1 and big_f(z, phi) == 0
    return z, phi, _flip_correction(z, phi)


def _h(k: int, nodes: list[Fraction]) -> Fraction:
    """The complete homogeneous symmetric polynomial ``h_k`` at ``nodes``."""
    if not nodes:
        return Fraction(int(k == 0))
    head, rest = nodes[0], nodes[1:]
    return sum((head**i * _h(k - i, rest) for i in range(k + 1)), Fraction(0))


def test_family_near_one() -> None:
    """``thm:familyone``: along (r, 3, 5, 7), ``inf b_2 - 24`` is of order
    ``(r - 1)^alpha``, ``alpha = log(5/3)/log 3``, near ``r = 1``.

    The closed forms of ``lem:threenode`` are identities of rational functions
    in ``A = 3^-x``, ``B = 5^-x``, ``C = 7^-x``: multiplied by ``D`` each side
    is a polynomial of degree at most 2 in each variable, so agreement on a
    4 x 4 x 4 grid proves it.  The bounds for ``x >= 4`` reduce to the rational
    inequalities checked here.  The flipped witness is built exactly at
    ``r = 101/100``, ``x = 6``.  Control: at ``x = 9`` the witness cannot start,
    and the certificate {1, 2, 9} costs less than ``t(9)/(1 + 3^(3-9))``.
    """
    # The closed forms as identities in (A, B, C).
    for a3 in (Fraction(20), Fraction(21), Fraction(22), Fraction(23)):
        for b5 in (Fraction(1), Fraction(2), Fraction(3), Fraction(4)):
            for c7 in (Fraction(1), Fraction(2), Fraction(3), Fraction(4)):
                lam, t, s1, sx = _three_node(a3, b5, c7)
                powers = [a3, b5, c7]
                assert sum(lam) == 1
                assert sum(li * a for li, a in zip(lam, _FAST, strict=True)) == 0
                assert sum(li * p for li, p in zip(lam, powers, strict=True)) == 0
                tail = sum(
                    li * (p * a - (a**2 - p)) / (1 - a)
                    for li, a, p in zip(lam, _FAST, powers, strict=True)
                )
                assert tail == t
                for a, p in zip(_FAST, powers, strict=True):
                    known = -(a**2 - p) / (1 - a) + p * a / (1 - a)
                    assert s1 * a + sx * p + known == t
                d = 3 * a3 - 10 * b5 + 7 * c7
                gap = 5 * b5 - 7 * c7 - 45 * a3 * b5 + 84 * a3 * c7 - 35 * b5 * c7
                assert Fraction(1, 24) - t == gap / (12 * d)
    # ... and at the true powers: the certificate {1, x} and its tail.
    for x in range(2, 41):
        lam, t, s1, sx = _at_x(x)
        assert lam == _certificate(_FAST, [1, x])
        assert t == _tail_of(_FAST, [1, x])
        d = Fraction(3, 3**x) - Fraction(10, 5**x) + Fraction(7, 7**x)
        assert d == Fraction(8, 105) * _h(x - 2, _FAST)
    assert _at_x(2)[1] == Fraction(1, 48) and _at_x(3)[1] == Fraction(31, 1704)
    # The bounds for x >= 4 (beta = (3/5)^x, gamma = (3/7)^x, gamma/beta =
    # (5/7)^x, A = 3^-x): each factor below is the worst case at x = 4 (x = 6).
    b4, g4, q4, a4 = (
        Fraction(3, 5) ** 4,
        Fraction(3, 7) ** 4,
        Fraction(5, 7) ** 4,
        Fraction(1, 81),
    )
    assert 1 - 36 * a4 - 56 * g4 * a4 > 0  # s_x > 0
    assert (1 + 90 * a4 * b4) / (6 * (3 - 10 * b4)) <= Fraction(1, 8)  # s_x
    assert 11 - 60 * b4 - 280 * a4 * g4 > 0  # s_1 > 0
    assert 20 - 21 * q4 - 210 * a4 - 70 * a4 * g4 > 0  # s_1 <= 1/2
    low = (5 - 7 * q4 - 45 * a4 - 35 * a4 * g4) / (12 * (3 + 7 * g4))
    assert low >= Fraction(1, 16)
    b6, q6, a6 = Fraction(3, 5) ** 6, Fraction(5, 7) ** 6, Fraction(1, 729)
    assert (5 + 84 * a6 * q6) / (12 * (3 - 10 * b6)) <= Fraction(1, 6)
    for x in range(4, 61):
        _, t, s1, sx = _at_x(x)
        gap = Fraction(1, 24) - t
        assert 0 < s1 <= Fraction(1, 2) and 0 < sx <= Fraction(3**x, 8)
        assert gap >= Fraction(1, 16) * Fraction(3, 5) ** x
        if x >= 6:  # and the upper bound of thm:familyone (c) at x = x_r
            assert gap <= Fraction(1, 6) * Fraction(3, 5) ** x
            upper = (1 + Fraction(27, 3**x)) / t
            assert upper <= 24 + 121 * Fraction(3, 5) ** x
    # The certificate {1, 2}: W_d = h_{d-3}(1/3, 1/5, 1/7)/105, tail 1/48.
    w = _certificate(_FAST, [1, 2])
    for d in range(3, 26):
        assert _u(_FAST, w, d) == _h(d - 3, _FAST) / 105
        assert _h(d - 3, _FAST) <= Fraction(35, 8) / 3 ** (d - 3)
    assert _tail_of(_FAST, [1, 2]) == Fraction(1, 48)
    # H' (weight 1 on 1/r, zero at 0, 1, 2) is prod(y - a_i) h_{d-3}(a, y), and
    # the certificate {1, 2, x} costs at most 1/48 + (315/128)(r/3)^x/(r^2(r-1)).
    for r in (Fraction(101, 100), Fraction(11, 10), Fraction(3, 2), Fraction(2)):
        nodes = [1 / r, *_FAST]
        hp = _correction(nodes, [1, 2])
        lead = (1 / r - _FAST[0]) * (1 / r - _FAST[1]) * (1 / r - _FAST[2])
        for d in range(3, 16):
            assert _u(nodes, hp, d) == lead * _h(d - 3, [*_FAST, 1 / r])
        for x in range(3, 16):
            bound = Fraction(1, 48) + Fraction(315, 128) * (r / 3) ** x / (
                r**2 * (r - 1)
            )
            assert _tail_of(nodes, [1, 2, x]) <= bound, (r, x)
    # The correction: |c_j| <= (13, 146, 405)_j 3^-z for z >= 7.
    inverse = [
        _solve(
            [[a, a**2, a**3] for a in _FAST], [Fraction(int(i == k)) for i in range(3)]
        )
        for k in range(3)
    ]  # inverse[k][j]: the entry (j, k) of the inverse matrix
    weights = [
        3,
        Fraction(5, 2) * Fraction(3, 5) ** 7,
        Fraction(7, 3) * Fraction(3, 7) ** 7,
    ]
    for j, cap in enumerate((13, 146, 405)):
        assert sum(abs(inverse[k][j]) * weights[k] for k in range(3)) <= cap
    # The flipped witness at r = 101/100 and x = x_r = 6.
    r = Fraction(101, 100)
    eps, y = r - 1, 1 / r
    assert 3**6 <= 8 / (r * eps) - 48 < 3**7 and 3**6 >= 1 / eps
    x = 6
    _, t, s1, sx = _at_x(x)
    assert y**x * (1 + y) - y**2 >= (1 - y) / 24  # (W1)
    assert 1 / (r * eps) >= 6 + Fraction(3**x, 8)  # (W2) at z_0 = x + 3
    lhs = y**2 + 2 * y ** (x + 3) - y**x - y ** (x + 1)
    assert lhs >= (1 - y) * (1 + Fraction(3**x, 8))
    # T > 5/192, so a worst placement costs more than the far ones.
    floor = (Fraction(1, 24) - Fraction(3, 5) ** 6 / 6) / (1 + Fraction(1, 27))
    assert floor > Fraction(5, 192) > max(Fraction(1, 48), Fraction(31, 1704))
    found = _flip_witness(r, x)
    assert found is not None
    z, phi, c = found
    assert z >= x + 3
    for cj, cap in zip(c, (13, 146, 405), strict=True):
        assert abs(cj) <= cap * Fraction(1, 3**z)
    rho = {1: s1 + c[0], 2: -1 + c[1], 3: -1 + c[2], x: sx, z: 1 - 2 * phi}
    for a in [y, *_FAST]:  # the series of w vanishes at all four nodes
        head = sum(rho.get(d, -1 if d < x else 1) * a**d for d in range(1, z + 1))
        assert 1 - (head - a ** (z + 1) / (1 - a)) / t == 0
    top = max(abs(v) for d, v in rho.items() if d != x)
    assert abs(rho[1]) <= 1 and top <= 1 + Fraction(1, 3 ** (z - 6))
    lower = t / (1 + Fraction(1, 3 ** (x - 3)))
    assert _tail_of([y, *_FAST], [1, x, z]) >= t / top >= lower
    # The two bounds of the theorem at r = 101/100: X and 3^X < 523/eps.
    big_x = 4
    while Fraction(315, 128) * (r / 3) ** (big_x + 1) > r**2 * eps / 192:
        big_x += 1
    assert 3**big_x < 523 / eps
    assert 24 + 36 * Fraction(3, 5) ** big_x < (1 + Fraction(1, 27)) / t
    # Control: at x = 9 the witness cannot start, and {1, 2, 9} undercuts the
    # bound the witness would give.
    assert _flip_witness(r, 9) is None
    t9 = _at_x(9)[1]
    assert _tail_of([y, *_FAST], [1, 2, 9]) < t9 / (1 + Fraction(1, 3**6))


def _gap_ratio(x: int) -> Fraction:
    """``R(x) = (36/5)(5/3)^x (1/24 - t(x))`` of ``lem:eighteen``."""
    return Fraction(36, 5) * Fraction(5, 3) ** x * (Fraction(1, 24) - _at_x(x)[1])


def _k_ratio(c: int) -> Fraction:
    """``K_c = ell(c) / (1/24 - t(c))`` of ``lem:eighteen``."""
    lam, t, _, _ = _at_x(c)
    return lam[0] / (Fraction(1, 24) - t)


def _exact_witness(y: Fraction, x: int, z: int) -> list[Fraction]:
    """``s_1, s_x, s_z, theta`` of the witness of the full certificate with
    zero set {1, x, z} on (y, 1/3, 1/5, 1/7): the pattern is ``s_1``, then -1
    below ``x``, ``s_x``, then +1 below ``z``, ``s_z``, then -1, and
    ``sum_d rho_d a^d = theta`` at the four nodes (``eq:witness``)."""
    rows, rhs = [], []
    for a in [y, *_FAST]:
        known = (a ** (x + 1) - a**z - a ** (z + 1) - a**2 + a**x) / (1 - a)
        rows.append([a, a**x, a**z, Fraction(-1)])
        rhs.append(-known)
    return _solve(rows, rhs)


def _cheap_bound(r: Fraction, c: int, x: int) -> Fraction:
    """The bound of ``lem:eighteen`` (b) on the cost of the placement ``x``."""
    lam, t, _, _ = _at_x(c)
    head = lam[0] / 3**x + lam[2] / 7**x
    return t + Fraction(35, 24) * head / _h(x - 2, _FAST[1:] + [Fraction(1)]) * (
        r ** (x - 1) / (r - 1)
    )


def test_family_oscillation() -> None:
    """``lem:eighteen`` and ``thm:familyosc``: along (r, 3, 5, 7) the excess
    ``inf b_2 - 24`` is ``(80 + o(1))(3/5)^x*`` off the jumps, ``x*`` the
    largest integer with ``3^x (r - 1) < 18``, so ``(inf b_2 - 24)(r-1)^-alpha``
    oscillates between ``80 * 18^-alpha`` and ``(400/3) 18^-alpha``.

    Checked: the solution of the corrected witness and its constants 15, 6,
    14; the identity behind the start of the path; the closed forms of
    ``18 * 3^-x s_x``, ``R(x)`` and ``K_c`` and their limits; the sum ``g`` of
    part (b).  At ``r = 5701/5700`` the infimum is found exactly:
    ``x* = 10``, the worst placement is {10} with zero set {1, 10, 1335},
    and every other placement costs less.  Control: ``t(11) > t(10)``, so
    the placement 11 is beaten only by the node ``1/r`` (part (b)), and the
    certificate {1, 4, 11} at ``(3, 5, 7)`` alone (``K_4 > 18``) costs more
    than ``t(10)``; and at ``x = 11``, ``3^11 (r - 1) > 18``, the witness
    condition of part (a) fails.
    """
    # (a) The corrected witness: p, q, theta' solve p a + q a^x - theta' =
    # delta(a) at the fast nodes, for each unit vector delta.
    for x in range(4, 13):
        a3, b5, c7 = Fraction(1, 3**x), Fraction(1, 5**x), Fraction(1, 7**x)
        d = 3 * a3 - 10 * b5 + 7 * c7
        assert d >= Fraction(17, 10) * a3
        for k in range(3):
            delta = [Fraction(int(i == k)) for i in range(3)]
            q = (3 * delta[0] - 10 * delta[1] + 7 * delta[2]) / d
            p = (
                -Fraction(105, 2)
                * (delta[0] * (b5 - c7) - delta[1] * (a3 - c7) + delta[2] * (a3 - b5))
                / d
            )
            theta = p / 3 + q * a3 - delta[0]
            for a in _FAST:
                assert p * a + q * a**x - theta == delta[_FAST.index(a)]
    cap_p = Fraction(525, 17) * (
        3 * Fraction(3, 5) ** 4
        + Fraction(5, 2) * Fraction(3, 5) ** 7
        + Fraction(7, 3) * Fraction(3, 7) ** 7
    )
    cap_q = Fraction(10, 17) * (9 + Fraction(49, 3) * Fraction(3, 7) ** 7)
    assert cap_p <= 15 and cap_q <= 6 and 25 * Fraction(3, 5) ** 2 <= 9
    assert Fraction(15, 3) + 6 + 3 == 14
    assert Fraction(1, 2) + Fraction(15, 3**7) < 1 and Fraction(6, 27) < 1
    for yv in (Fraction(1, 2), Fraction(9, 10), Fraction(100, 101)):
        for x in range(4, 9):
            lhs = yv**2 + 2 * yv ** (x + 3) - yv**x - yv ** (x + 1)
            assert lhs == yv**2 - (1 - yv) * yv**x * (2 * yv**2 + 2 * yv + 1)
    # (c) The closed forms and limits.
    for x in range(4, 61):
        _, t, _, sx = _at_x(x)
        beta, gamma = Fraction(3, 5) ** x, Fraction(3, 7) ** x
        den = 1 - Fraction(10, 3) * beta + Fraction(7, 3) * gamma
        a3, c7, q57 = Fraction(1, 3**x), Fraction(1, 7**x), Fraction(5, 7) ** x
        assert 18 * a3 * sx == (1 - 36 * a3 + Fraction(90, 5**x) - 56 * c7) / den
        num = 1 - Fraction(7, 5) * q57 - 9 * a3 + Fraction(84, 5) * a3 * q57 - 7 * c7
        assert _gap_ratio(x) == num / den
        assert _gap_ratio(x) >= Fraction(9, 20)
    assert abs(18 * _at_x(60)[3] / 3**60 - 1) < Fraction(1, 10**12)
    assert abs(_gap_ratio(60) - 1) < Fraction(1, 10**8)
    for c in range(2, 61):
        assert _k_ratio(c) > 18
    assert _k_ratio(60) - 18 < Fraction(1, 10**8)
    # (b) g_d = (y - 1/5)(y - 1/7) h_{d-2}(1/5, 1/7, y), and its sum.
    for r in (Fraction(101, 100), Fraction(3, 2)):
        yv = 1 / r
        for dd in range(0, 12):
            g = yv**dd - (35 * yv - 5) / 2 / 5**dd + (35 * yv - 7) / 2 / 7**dd
            lead = (yv - Fraction(1, 5)) * (yv - Fraction(1, 7))
            assert g == (lead * _h(dd - 2, [*_FAST[1:], yv]) if dd >= 2 else 0)
        total = sum(
            w / (1 - a)
            for w, a in zip(
                (1, -(35 * yv - 5) / 2, (35 * yv - 7) / 2),
                (yv, Fraction(1, 5), Fraction(1, 7)),
                strict=True,
            )
        )
        assert total == Fraction(35, 24) * lead / (1 - yv)
    # The exact infimum at r = 5701/5700.
    r = Fraction(5701, 5700)
    eps, y = r - 1, 1 / r
    assert 3**10 * eps < 18 < 3**11 * eps
    x, z = 10, 1335
    _, t, s1, sx = _at_x(x)
    assert y**x * (1 + y) - y**2 >= (1 - y) / 24 and sx + 7 <= 1 / (r * eps)
    ws1, _, wsz, theta = _exact_witness(y, x, z)
    assert abs(ws1) <= 1 and abs(wsz) <= 1  # eq:witness: tau({10}) = theta
    cert = _certificate([y, *_FAST], [1, x, z])
    tail = sum(
        li * (a ** (x + 1) - a**z - a ** (z + 1) - a**2 + a**x) / (1 - a)
        for li, a in zip(cert, [y, *_FAST], strict=True)
    )
    assert tail == theta  # the signed sum is the tail (sign pattern of v)
    assert 0 < t - theta <= 14 * Fraction(1, 3**z) < Fraction(1, 10**600)
    assert all(_at_x(k)[1] < theta for k in range(4, 10))
    assert max(Fraction(1, 48), Fraction(31, 1704)) < theta
    for k in range(11, 20):  # decreasing in x, so x = 11 covers all x >= 11
        assert _cheap_bound(r, 4, k + 1) < _cheap_bound(r, 4, k)
    assert _cheap_bound(r, 4, 11) < Fraction(3593, 100000) < theta
    assert Fraction(2447884, 100000) < 1 / theta < Fraction(2447885, 100000)
    # Controls: t(11) > t(10), so the trivial bound leaves the placement 11
    # open; below 18 part (b) is useless (K_c > 18); at x = 11 the witness
    # condition of part (a) fails.
    assert _at_x(11)[1] > t
    assert all(_cheap_bound(r, c, x) > t for c in range(2, x))
    assert _at_x(11)[3] + 7 > 1 / (r * eps)


# --- One placement exactly, the limit profile and the jumps -------------------


def _kernel_weights(x: int):
    """The weights on (1/3, 1/5, 1/7) of ``U = U^(x)``, ``V`` (values 0, 1, 0 at
    ``d = 0, 1, x``) and ``V'`` (values 0, 0, 1) of ``thm:familyzero``."""
    a3, b5, c7 = Fraction(1, 3**x), Fraction(1, 5**x), Fraction(1, 7**x)
    d = 3 * a3 - 10 * b5 + 7 * c7
    lam = _at_x(x)[0]
    v = [
        -105 * (b5 - c7) / (2 * d),
        -105 * (c7 - a3) / (2 * d),
        -105 * (a3 - b5) / (2 * d),
    ]
    vp = [3 / d, -10 / d, 7 / d]
    return lam, v, vp


def _from(w: list[Fraction], z: int) -> Fraction:
    """``sum_{d >= z}`` of the exponential sum with weights ``w`` on the fast nodes."""
    return sum(wi * a**z / (1 - a) for wi, a in zip(w, _FAST, strict=True))


class _Placement:
    """The kernel ``H``, the mass ``F`` and the half-mass point of
    ``thm:familyzero`` for the placement ``x`` at ``r``."""

    def __init__(self, r: Fraction, x: int) -> None:
        self.r, self.x, self.y = r, x, 1 / r
        self.lam, self.v, self.vp = _kernel_weights(x)
        _, self.t, self.s1, self.sx = _at_x(x)
        y = self.y
        self.big_f = (
            self.s1 * y
            + self.sx * y**x
            + (y**x + y ** (x + 1) - y**2) / (1 - y)
            - self.t
        )

    def u(self, d: int) -> Fraction:
        return _u(_FAST, self.lam, d)

    def h(self, d: int) -> Fraction:
        y, x = self.y, self.x
        return (
            y**d - self.u(d) - y * _u(_FAST, self.v, d) - y**x * _u(_FAST, self.vp, d)
        )

    def h_from(self, z: int) -> Fraction:
        """``sum_{d >= z} H_d`` for ``z > x``, a combination of geometric sums."""
        y, x = self.y, self.x
        return (
            y**z / (1 - y)
            - _from(self.lam, z)
            - y * _from(self.v, z)
            - y**x * _from(self.vp, z)
        )

    def cost(self) -> tuple[Fraction, list[int], Fraction]:
        """``tau({x})``, its zero set and ``phi`` by ``thm:familyzero`` (c)."""
        x, half = self.x, self.big_f / 2
        if self.h_from(x + 1) >= half:  # z > x: bisect the decreasing tail sums
            lo, hi = x + 1, x + 2
            while self.h_from(hi) >= half:
                lo, hi = hi, 2 * hi
            while hi - lo > 1:
                mid = (lo + hi) // 2
                lo, hi = (mid, hi) if self.h_from(mid) >= half else (lo, mid)
            z = lo
            phi = (half - self.h_from(z + 1)) / self.h(z)
            tau = self.t - 2 * _from(self.lam, z + 1) - 2 * phi * self.u(z)
            return tau, [1, x, z], phi
        before = self.h_from(x + 1)
        loss = 2 * _from(self.lam, x + 1)
        for z in range(x - 1, 1, -1):
            if before + abs(self.h(z)) >= half:
                phi = (half - before) / abs(self.h(z))
                return self.t - loss - 2 * phi * abs(self.u(z)), [1, z, x], phi
            before += abs(self.h(z))
            loss += 2 * abs(self.u(z))
        raise AssertionError("F/2 exceeds the mass of H")


def _witness_rho(p: _Placement, zeros: list[int], phi: Fraction):
    """The flipped witness of the proof of ``thm:familyzero`` (c): entries at
    the positions up to ``max(zeros) + 1`` (``sigma`` flipped on ``Pi(z)``,
    ``1 - 2 phi`` times ``sigma`` at ``z``), then -1, with ``rho_1``, ``rho_x``
    from the pairing with ``V`` and ``V'``."""
    x, z = p.x, (zeros[2] if zeros[1] == p.x else zeros[1])
    top = max(zeros) + 1

    def sigma(d: int) -> int:
        return -1 if d < x else 1

    def flipped(d: int) -> Fraction:
        if (z > x and d > z) or (z < x and (d > x or z < d < x)):
            return Fraction(1)
        return phi if d == z else Fraction(0)

    rho = {}
    for d in range(2, top + 1):
        if d != x:
            rho[d] = sigma(d) * (1 - 2 * flipped(d))
    # Past ``top`` every entry is -1 (flipped past x).  The pairing with V
    # and V' (``sum_d rho_d V_d = 0`` etc.) fixes rho_1 and rho_x.
    for key, w in ((1, p.v), (x, p.vp)):
        head = sum(rho[d] * _u(_FAST, w, d) for d in rho)
        rho[key] = -(head - _from(w, top + 1))
    return rho, top


def test_family_zero_sets() -> None:
    """``thm:familyzero``: along (r, 3, 5, 7), for every placement ``x >= 2``
    and ``1 < r < 3``, the minimising zero set is {1, x, z} or {1, z, x}, with
    ``z`` the half-mass point of ``|H|`` flipped from the far end.

    Checked exactly: the weights of ``V`` and ``V'``, the basis identity
    ``a^d = U_d + V_d a + V'_d a^x``, the zeros and signs of ``H``, ``U``,
    ``V``, the identities ``sum |V_d| = s_1`` and ``sum |H_d| = F > 0`` (and
    the polynomial ``p`` of the Descartes argument); at several ``r`` and
    ``x`` the flipped witness has entries in [-1, 1] off ``x`` and sums to the
    tail at all four nodes, and no zero set with entries up to 16 does better.
    The costs of ``thm:familylow`` and ``thm:elevenvalue`` come out, and at
    ``r = 5701/5700`` the zero set {1, 10, 1335} of ``thm:familyosc``.
    Control: moving the third zero one step either way costs more, and
    ``sum_{d > x} V'_d < 1`` fails at ``x = 2``.
    """
    assert _at_x(2)[2] == Fraction(7, 24) and _at_x(3)[2] == Fraction(859, 3408)
    assert _at_x(2)[3] == Fraction(-19, 16) and _at_x(3)[3] == Fraction(821, 1136)
    for x in range(2, 16):
        lam, v, vp = _kernel_weights(x)
        _, t, s1, sx = _at_x(x)
        assert 0 < s1 <= Fraction(1, 2)
        assert v == _solve([[a**d for a in _FAST] for d in (0, 1, x)], [0, 1, 0])
        assert vp == _solve([[a**d for a in _FAST] for d in (0, 1, x)], [0, 0, 1])
        for d in range(0, 20):
            if d >= 2:
                assert _u(_FAST, vp, d) == _h(d - 2, _FAST) / _h(x - 2, _FAST)
            for a in _FAST:
                parts = (
                    _u(_FAST, lam, d) + _u(_FAST, v, d) * a + _u(_FAST, vp, d) * a**x
                )
                assert parts == a**d
        # sum_{d >= 2, d != x} |V_d| = s_1, with V > 0 below x and < 0 past it.
        below = [_u(_FAST, v, d) for d in range(2, x)]
        assert all(b > 0 for b in below) and _u(_FAST, v, x + 1) < 0
        assert sum(below, Fraction(0)) - _from(v, x + 1) == s1
        # The polynomial p of the Descartes argument: p(1) = 1, zero at the nodes.
        coeffs = {0: -t, 1: s1 + t, 2: -(s1 + 1)}
        coeffs[x] = coeffs.get(x, 0) + sx + 1
        coeffs[x + 1] = coeffs.get(x + 1, 0) + 1 - sx
        assert sum(coeffs.values()) == 1
        for a in _FAST:
            assert sum(c * a**k for k, c in coeffs.items()) == 0
        if x >= 3:  # Theorem thm:familylimit uses sum_{d > x} V'_d < 1.
            assert 0 < _from(vp, x + 1) < 1
    assert _from(_kernel_weights(2)[2], 3) > 1  # control: fails at x = 2
    # The kernel at several r: zeros, signs, and sum |H_d| = F > 0.
    for r in (Fraction(101, 100), Fraction(5, 4), Fraction(2), Fraction(29, 10)):
        for x in range(2, 10):
            p = _Placement(r, x)
            assert p.h(0) == p.h(1) == p.h(x) == 0
            for d in range(2, x + 12):
                if d != x:
                    assert (p.h(d) > 0) == (d > x) and (p.u(d) > 0) == (d > x)
            mass = sum((abs(p.h(d)) for d in range(2, x)), Fraction(0))
            assert mass + p.h_from(x + 1) == p.big_f > 0
    # Exact minimisers: the witness certifies the half-mass zero set.
    for r, xs in (
        (Fraction(5, 4), (2, 4, 6)),
        (Fraction(2), (3, 5)),
        (Fraction(11, 10), (5,)),
    ):
        nodes = [1 / r, *_FAST]
        for x in xs:
            p = _Placement(r, x)
            tau, zeros, phi = p.cost()
            assert 0 < phi <= 1
            assert _tail_of(nodes, sorted(zeros)) == tau
            rho, top = _witness_rho(p, zeros, phi)
            assert all(abs(val) <= 1 for d, val in rho.items() if d != x)
            for a in nodes:
                head = sum(rho[d] * a**d for d in rho)
                assert head - a ** (top + 1) / (1 - a) == tau
            best = min(
                _tail_of(nodes, sorted({i, j, x}))
                for i in range(1, 17)
                for j in range(i + 1, 17)
                if len({i, j, x}) == 3
            )
            assert best >= tau
            # Control: the neighbouring third zeros cost more (phi < 1 here).
            third = zeros[2] if zeros[1] == x else zeros[1]
            for other in (third - 1, third + 1):
                if other >= 2 and other != x:
                    assert _tail_of(nodes, sorted({1, x, other})) > tau
    # The costs of thm:familylow and thm:elevenvalue.
    tau, zeros, _ = _Placement(Fraction(5, 4), 4).cost()
    assert (tau, zeros) == (Fraction(7627, 314024), [1, 4, 5])
    tau, zeros, _ = _Placement(Fraction(11, 10), 5).cost()
    assert (tau, zeros) == (Fraction(96935, 3398808), [1, 3, 5])
    # r = 5701/5700: the half-mass point of the placement 10 is 1335.
    p = _Placement(Fraction(5701, 5700), 10)
    assert p.h_from(1336) < p.big_f / 2 <= p.h_from(1335)


def _limit_k(c: int) -> Fraction:
    """The breakpoint ``k_c`` of ``thm:familylimit``."""
    return 18 / (1 - Fraction(18, 3**c) + Fraction(30, 5**c) - Fraction(14, 7**c))


def _m_sum(c: int) -> Fraction:
    """``M_c = 2 sum_{d >= c} g_d``."""
    return Fraction(3, 3**c) - Fraction(25, 3 * 5**c) + Fraction(49, 9 * 7**c)


def test_family_jumps() -> None:
    """``thm:familylimit``, ``thm:familyjump`` and ``prop:familyrdelta``.

    Checked: the identities behind the profile ``G`` (as polynomial
    identities in ``A = 3^-c``, ``B = 5^-c``, ``C = 7^-c`` on a grid), the
    breakpoints ``k_c`` decreasing to 18 with ``k_3 = 66150/1957``, that on
    each piece the certificate {1, c} lifted to ``r`` is the least of the
    limits ``t(c') + ell(c')/kappa``, and the constants of the proofs.  Two
    exact switches: at ``r = 101/100`` the worst placement is 7 = ``x* + 1``
    with zero set {1, 4, 7}, and at ``r = 9842/9841`` it is 11 with
    {1, 7, 11}.  Controls: ``c = 2`` is never the least, below 18 every
    ``t(c) + ell(c)/kappa`` exceeds 1/24, and at ``r = 101/100`` the far flips
    alone cannot balance the placement 7.
    """
    # The identities (eq:profileid), times D, on a 4 x 4 x 4 grid.
    for a3 in (Fraction(20), Fraction(21), Fraction(22), Fraction(23)):
        for b5 in (Fraction(1), Fraction(2), Fraction(3), Fraction(4)):
            for c7 in (Fraction(1), Fraction(2), Fraction(3), Fraction(4)):
                lam, t, _, _ = _three_node(a3, b5, c7)
                d = 3 * a3 - 10 * b5 + 7 * c7
                g, uinf = d / 3, (5 * b5 - 7 * c7) / 2
                assert uinf == lam[0] * g
                m_c = 3 * a3 - Fraction(25, 3) * b5 + Fraction(49, 9) * c7
                rest = Fraction(25, 4) * b5 - Fraction(49, 6) * c7
                assert t + lam[0] * (Fraction(1, 18) - m_c) == Fraction(1, 24) - rest
    for c in range(2, 41):
        a3, b5, c7 = Fraction(1, 3**c), Fraction(1, 5**c), Fraction(1, 7**c)
        uinf = [
            Fraction(7, 2) * Fraction(1, 7**d) - Fraction(5, 2) * Fraction(1, 5**d)
            for d in range(c, c + 3)
        ]
        assert all(u < 0 for u in uinf)
        tail = Fraction(25, 4) * b5 - Fraction(49, 6) * c7  # 2 sum_{d >= c} |U^inf_d|
        assert tail == 2 * (
            Fraction(5, 2) * b5 * Fraction(5, 4) - Fraction(7, 2) * c7 * Fraction(7, 6)
        )
        assert _m_sum(c) - _m_sum(c + 1) == 2 * (
            a3 - Fraction(10, 3) * b5 + Fraction(7, 3) * c7
        )
        if c >= 3:
            assert 1 / _limit_k(c) == Fraction(1, 18) - _m_sum(c + 1)
            assert 18 < _limit_k(c + 1) < _limit_k(c)
    assert _limit_k(3) == Fraction(66150, 1957)
    assert _m_sum(3) == Fraction(19, 315) and _m_sum(4) < Fraction(1, 18) < _m_sum(3)
    assert 1 - Fraction(18, 9) + Fraction(30, 25) - Fraction(14, 49) < 0  # no k_2
    assert _limit_k(40) - 18 < Fraction(1, 10**15)

    # On each piece the least t(c') + ell(c')/kappa is at c' = c, never at 2;
    # below 18 all exceed 1/24.
    def lifted(c: int, kappa: Fraction) -> Fraction:
        lam, t, _, _ = _at_x(c)
        return t + lam[0] / kappa

    for c in range(3, 12):
        hi = _limit_k(c - 1) if c > 3 else Fraction(60)
        for kappa in (_limit_k(c), (_limit_k(c) + hi) / 2):
            values = {cc: lifted(cc, kappa) for cc in range(2, 30)}
            assert min(values.values()) == values[c] < Fraction(1, 24)
            assert values[2] > values[c]
    for kappa in (Fraction(6), Fraction(18)):
        assert all(lifted(cc, kappa) > Fraction(1, 24) for cc in range(2, 30))
    # Constants of the proofs.
    assert _at_x(3)[0][0] == Fraction(81, 142)
    for c in range(3, 61):
        lam, t, _, _ = _at_x(c)
        assert lam[0] <= 5 * Fraction(3, 5) ** c and lam[0] <= 1
        assert lam[1] <= Fraction(-5, 2) and 0 < lam[2] <= 7
        if c >= 4:
            a3, b5, c7 = Fraction(1, 3**c), Fraction(1, 5**c), Fraction(1, 7**c)
            q = (45 * a3 * b5 - 84 * a3 * c7 + 35 * b5 * c7) / (5 * b5 - 7 * c7)
            assert (
                q
                <= (45 * a3 + 35 * c7) / (5 - 7 * Fraction(5, 7) ** c)
                <= Fraction(146, 10) * a3
            )
            assert _k_ratio(c) == 18 / (1 - q) <= 18 * (1 + 18 * a3)
            assert (
                lam[2] / lam[0]
                <= 7 * a3 / (5 * b5 - 7 * c7)
                <= Fraction(23, 10) * Fraction(5, 3) ** c
            )
            d = 3 * a3 - 10 * b5 + 7 * c7
            assert d >= Fraction(17, 10) * a3
            assert abs(lam[1] + Fraction(5, 2)) <= 15 * Fraction(3, 5) ** c
            assert abs(lam[2] - Fraction(7, 2)) <= 15 * Fraction(3, 5) ** c
            assert lam[0] <= 15 * Fraction(3, 5) ** c
        if c >= 3:  # M_{c+1} >= (5/8) 3^-c and M_c <= 4 * 3^-c
            assert _m_sum(c + 1) >= Fraction(5, 8) / 3**c and _m_sum(c) <= Fraction(
                4, 3**c
            )
    for x in range(11, 61):  # 0.96 <= R(x) <= 1.02 and the bound 18 3^-x s_x
        assert Fraction(96, 100) <= _gap_ratio(x) <= Fraction(102, 100)
        if x >= 12:
            beta = Fraction(3, 5) ** x
            assert 18 * _at_x(x)[3] / 3**x <= 1 + 4 * beta
    assert 3 * 49 > 144 and 3**12 < 960000 < 3**13  # 3^(-1/2) < 7/12; x >= 13
    # The switch at r = 101/100: x* = 6, the worst placement is 7.
    r = Fraction(101, 100)
    eps = r - 1
    assert 3**6 * eps < 18 <= 3**7 * eps
    nodes = [1 / r, *_FAST]
    tau6, z6, _ = _Placement(r, 6).cost()
    p7 = _Placement(r, 7)
    tau7, z7, phi7 = p7.cost()
    assert z6 == [1, 6, 41] and z7 == [1, 4, 7] and 0 < phi7 < 1
    assert _tail_of(nodes, z6) == tau6 and _tail_of(nodes, z7) == tau7
    assert 2 * p7.h_from(8) < p7.big_f  # control: far flips alone do not balance
    assert max(_at_x(4)[1], _at_x(5)[1]) < _at_x(6)[1] < tau7 and tau6 < tau7
    assert max(Fraction(1, 48), Fraction(31, 1704)) < tau7
    for k in range(8, 20):
        assert _cheap_bound(r, 3, k + 1) < _cheap_bound(r, 3, k)
    assert _cheap_bound(r, 3, 8) < Fraction(2761, 100000) < tau7
    assert Fraction(278209, 10000) < 1 / tau7 < Fraction(27821, 1000)
    # The switch at r = 9842/9841: x* = 10, the worst placement is 11.
    r = Fraction(9842, 9841)
    eps = r - 1
    assert 3**10 * eps < 18 <= 3**11 * eps
    tau11, z11, _ = _Placement(r, 11).cost()
    assert z11 == [1, 7, 11] and _tail_of([1 / r, *_FAST], z11) == tau11
    assert all(_at_x(k)[1] < tau11 for k in range(4, 11))
    assert Fraction(408515, 10**7) < _at_x(10)[1] < Fraction(408516, 10**7)
    for k in range(12, 24):
        assert _cheap_bound(r, 3, k + 1) < _cheap_bound(r, 3, k)
    assert _cheap_bound(r, 3, 12) < Fraction(288, 10000) < tau11
    assert Fraction(243009, 10000) < 1 / tau11 < Fraction(24301, 1000)


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
