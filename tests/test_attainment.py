"""Exact checks of ``sec:extremal`` in ``coefficient-mass-attainment.tex``.

At roots at least 2 the escaping placement is extremal (``thm:extremal``):
the minimiser for the smaller placement is lifted by one node, directly when
the new zero is aligned (``lem:delete``) and through the run chord
(``prop:runchord``) when it straddles.  Below 2 the conclusion fails
(``prop:belowtwo``).

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

from tests.sweep import _certificate, _partial_sums, _tail, _u, min_bk_of

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
    """Both sides of ``eq:runchord``: ``Tail(F)`` and the combination."""
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
    # q = sum lambda_j F_j + mu w must vanish on Z, as in the proof.
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
    sums = _partial_sums([Fraction(r) for r in (3, 5, 7)] + [Fraction(-9, 62)])
    assert max(abs(v) for v in sums[1:]) == 1 / tau
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
