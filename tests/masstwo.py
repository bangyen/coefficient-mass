"""The ``L**2`` constant at ``(x-2)**L``, narrowed.

Run:  just masstwo   (or python tests/masstwo.py); ``just test`` runs each
check as a pytest test.

``coefficient-mass.tex`` gives the elementary uniform bound ``L**2/80``
(``prop:quadratic``) and the asymptotic Jensen constant below at ``r_i = 2``;
``Lambda((x-2)**L) ~ (1 + log 2)L**2/2`` is the upper bound from ``Q = 1``.
The checks here quantify where the improvement over the elementary constant
comes from.
``eq:jensen`` holds for *every* ``1/2 < R < 1`` and *every* row ``k``, and
``prop:quadratic`` spends it once: it fixes ``R = 9/10`` and keeps only the
rows ``k <= L/8``.

Most of the gap to ``1/80`` is not that spend but the closing estimate.
Evaluated exactly, ``R = 9/10`` over ``k <= L/8`` is already worth
``0.0509 L**2`` in the limit -- four times the constant it is rounded down to,
and the ``paper /L^2`` column below climbs towards it.  Choosing ``R`` per row
and keeping every row raises that to ``0.0647 L**2``, which is what this
method is worth.  Thus optimizing the elementary ``1/80`` proof improves
its constant by a factor of ``5.2``, of which
``1.27`` is the better ``R`` and the rest is arithmetic the paper did not
need.

Put ``R_k = 1 - k/L``, which the density below singles out and which keeps
``beta_k`` rational, so every number here is exact:

    beta_k = ((2 R_k)**(L-k+1) - 1) / ((1 - R_k)**(-k) - 1),
    Lambda(F) >= sum_k log+ beta_k,

the rows sitting at ``L`` distinct positions and ``f_D = 1`` contributing
nothing.  The finite checks show that the sum exceeds ``L**2/16`` at
``L = 97`` but not ``L = 96``, and exceeds ``L**2/20`` at ``L = 14``.

Its density explains the limit.  With ``alpha = k/L`` the summand is
``L phi(alpha) + O(1)``, where

    phi(alpha) = (1 - alpha) log(2 - 2 alpha) + alpha log alpha

is exactly what ``R = 1 - alpha`` maximises, so the sum is
``c L**2 + O(L log L)`` with ``c = int_0^a0 phi`` and ``phi(a0) = 0``:

    a0 = 0.2270921952...,   c = 0.0647068486...  >  1/16.

So ``liminf Lambda(F)/L**2 >= c`` over monic multiples, five times the
elementary ``1/80`` constant.  Nothing is assumed beyond ``eq:jensen``
itself; only the choice of ``R`` and the range of ``k`` change.

The upper end does not move the same way.  ``Q = 1`` is *not* optimal --
:func:`_check_witness` exhibits rational ``Q`` with
``Lambda((x-2)**L Q) < Lambda((x-2)**L)`` for every ``2 <= L <= 12``, verified
as an inequality between two integers.  In the finite search over
``Q = (x+1)**m`` at ``L = 20, 40, 80`` and ``m <= 2L``, the best tested
choice saves at most ``L``.  This is evidence about that tested family, not
a proof of its asymptotic behavior.  Independently, ``Q = 1`` gives the
rigorous upper constant ``(1 + log 2)/2 = 0.8465735...``.  The bracket is
therefore

    0.0647068... <= liminf M((x-2)**L)/L**2 <= limsup <= 0.8465735...,

narrowed at the bottom only, and whether the ratio converges stays open.

Every claim here is a positive statement, so each check carries a control
that must fail: the rows are checked against the order statistics of actual
multiples, and the witness search is re-run at ``Q = 1`` and at a ``Q`` that
must not win.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, log

#: Rows are compared against the order statistics of these multipliers, as
#: integer coefficient lists low-to-high, at every ``L`` of :data:`_ROW_L`.
_PROBES: tuple[tuple[int, ...], ...] = ((1,), (1, 1), (-1, 1), (0, 0, 1), (2, 3, 1))

#: Degrees at which the summed rows are tabulated.  The largest is the
#: exactness ceiling, not a mathematical one: ``beta_k`` at ``L = 512`` is a
#: ratio of integers with about 4600 bits.
_ROW_L: tuple[int, ...] = (8, 13, 14, 16, 32, 64, 96, 97, 128, 256, 512)

#: ``(L, denominator bound, Q as coefficients low-to-high, monic)``: the
#: multipliers beating ``Q = 1``, found by local search on ``Lambda`` over
#: ``deg Q <= 12`` and then rounded to the smallest denominator that still
#: wins.  ``L = 11`` is the telling one: ``Q = x**2 + x``, so ``x + 1`` alone
#: already beats the root product.
_WITNESS: dict[int, tuple[str, ...]] = {
    2: ("0", "0", "1", "1", "1", "1", "1", "1"),
    3: ("0", "1/3", "1/2", "2/3", "1", "1"),
    4: ("0", "0", "1/2", "1", "4/3", "4/3", "1"),
    5: ("0", "2/5", "1", "7/5", "1"),
    6: ("0", "1/4", "3/4", "3/2", "5/3", "1"),
    7: ("2/7", "1", "35/18", "32/11", "25/9", "1"),
    8: ("0", "2/3", "10/7", "1"),
    9: ("1/2", "16/13", "1"),
    10: ("1/7", "5/7", "29/19", "26/15", "1"),
    11: ("0", "1", "1"),
    12: ("14/23", "11/8", "1"),
}

#: ``Q`` values that must *not* beat ``Q = 1``, as the control on the search.
_LOSERS: tuple[tuple[str, ...], ...] = (("1",), ("-1", "1"), ("-2", "1"))


def _shifted(L: int) -> list[int]:
    """``(x-2)**L`` as integer coefficients, low-to-high."""
    poly = [1]
    for _ in range(L):
        nxt = [0] * (len(poly) + 1)
        for i, c in enumerate(poly):
            nxt[i] -= 2 * c
            nxt[i + 1] += c
        poly = nxt
    return poly


def _mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def _beta(L: int, k: int) -> Fraction | None:
    """``eq:jensen`` at ``R = 1 - k/L``, exactly, or ``None`` if ``R <= 1/2``."""
    R = Fraction(L - k, L)
    if 2 * R <= 1:
        return None
    num = (2 * R) ** (L - k + 1) - 1
    den = (1 - R) ** (-k) - 1
    return None if num <= 0 or den <= 0 else Fraction(num, 1) / den


def _row_sum(L: int) -> tuple[Fraction, int]:
    """``sum_k log+ beta_k`` as a product, with the number of rows used.

    The product is returned instead of the sum so the bound stays a
    comparison between rationals; ``log`` is applied only when printing.
    """
    prod, used = Fraction(1), 0
    for k in range(1, L):
        beta = _beta(L, k)
        if beta is None:
            break
        if beta > 1:
            prod *= beta
            used += 1
    return prod, used


def _paper_row_sum(L: int) -> Fraction:
    """The same sum as ``prop:quadratic`` spends it: ``R = 9/10``, ``k <= L/8``."""
    R, prod = Fraction(9, 10), Fraction(1)
    for k in range(1, L // 8 + 1):
        num = (2 * R) ** (L - k + 1) - 1
        den = (1 - R) ** (-k) - 1
        beta = Fraction(num, 1) / den
        if beta > 1:
            prod *= beta
    return prod


def _log(q: Fraction) -> float:
    return log(q.numerator) - log(q.denominator)


def _order_stats(poly: list[Fraction]) -> list[Fraction]:
    """Nonleading coefficient magnitudes, largest first: ``b_1, b_2, ...``."""
    return sorted((abs(c) for c in poly[:-1]), reverse=True)


def _mass_product(poly: list[Fraction]) -> Fraction:
    """``prod |f_j|`` over ``|f_j| > 1``, so that ``Lambda = log`` of it."""
    prod = Fraction(1)
    for c in poly:
        if abs(c) > 1:
            prod *= abs(c)
    return prod


def _root_product_mass(L: int) -> Fraction:
    """``prod_k e_k`` at ``r_i = 2``, so that ``Lambda((x-2)**L) = log`` of it."""
    prod = Fraction(1)
    for k in range(1, L + 1):
        prod *= comb(L, k) * 2**k
    return prod


def _check_rows(failures: list[str]) -> int:
    """Every row of ``eq:jensen`` at ``R = 1 - k/L``, summed and validated.

    Three things at once: the rows really do bound the order statistics of
    actual multiples (the control -- a misread of ``eq:jensen`` dies here),
    the summed bound clears ``L**2/16`` at ``L = 97`` but not ``96``, clears
    ``L**2/20`` at ``L = 14`` but not ``13``, and clears the stated bounds
    at the listed larger sample degrees.  It also beats what
    ``prop:quadratic`` spends at the same sampled ``L``.
    """
    checks = 0
    for L in _ROW_L:
        prod, used = _row_sum(L)
        if used == 0:
            failures.append(f"L={L}: no row of eq:jensen exceeds 1")
            continue
        total = _log(prod)
        if L >= 97 and total < L**2 / 16:
            failures.append(f"L={L}: summed rows {total:.3f} < L^2/16")
        if L == 96 and total >= L**2 / 16:
            failures.append(f"L={L}: control unexpectedly clears L^2/16")
        if L >= 14 and total < L**2 / 20:
            failures.append(f"L={L}: summed rows {total:.3f} < L^2/20")
        if L == 13 and total >= L**2 / 20:
            failures.append(f"L={L}: control unexpectedly clears L^2/20")
        if total < L**2 / 80:
            failures.append(f"L={L}: summed rows {total:.3f} below the paper's L^2/80")
        if prod <= _paper_row_sum(L):
            failures.append(f"L={L}: per-row R does not beat R=9/10 over k<=L/8")
        checks += 1

    # The control: beta_k must not exceed b_k(F) for an actual monic multiple.
    for L in _ROW_L[:4]:
        base = [Fraction(c) for c in _shifted(L)]
        for probe in _PROBES:
            stats = _order_stats(_mul(base, [Fraction(c) for c in probe]))
            for k in range(1, L):
                beta = _beta(L, k)
                if beta is None:
                    break
                if stats[k - 1] < beta:
                    failures.append(
                        f"L={L} Q={probe} k={k}: b_k={float(stats[k - 1]):.4g} "
                        f"< beta_k={float(beta):.4g}"
                    )
            checks += 1
    return checks


def _check_witness(failures: list[str]) -> int:
    """Rational ``Q`` beating ``Q = 1`` at every ``2 <= L <= 12``, exactly.

    ``Lambda`` is a sum of logarithms, so ``Lambda(PQ) < Lambda(P)`` is the
    inequality ``prod_{|f_j|>1}|f_j| < prod_k e_k`` between two rationals, and
    is decided without a single floating-point step.  The control re-runs the
    comparison at ``Q = 1`` (equality, not a win) and at the ``_LOSERS``.
    """
    checks = 0
    for L, entry in _WITNESS.items():
        base = [Fraction(c) for c in _shifted(L)]
        q = [Fraction(c) for c in entry]
        if q[-1] != 1:
            failures.append(f"L={L}: witness Q is not monic")
            continue
        mine = _mass_product(_mul(base, q))
        theirs = _root_product_mass(L)
        if mine >= theirs:
            failures.append(f"L={L}: witness does not beat Q=1")
        checks += 1

        if _mass_product(_mul(base, [Fraction(1)])) != theirs:
            failures.append(f"L={L}: Q=1 does not reproduce Lambda((x-2)^L)")
        for loser in _LOSERS:
            beaten = _mass_product(_mul(base, [Fraction(c) for c in loser]))
            if beaten < theirs:
                failures.append(f"L={L}: control Q={loser} unexpectedly beats Q=1")
        checks += 1
    return checks


def _check_family(failures: list[str]) -> int:
    """Check bounded searches over ``Q = (x+1)**m`` at three values of ``L``.

    For ``L = 20, 40, 80`` and ``m <= 2L``, the best tested multiplier must
    leave the normalized mass within ``1/L`` of ``Q = 1``.  This is a finite
    regression check, not an asymptotic theorem about the whole family.
    """
    checks = 0
    for L in (20, 40, 80):
        base = [Fraction(c) for c in _shifted(L)]
        theirs = _log(_root_product_mass(L))
        best, arg = theirs, 0
        poly = base
        for m in range(1, 2 * L + 1):
            poly = _mul(poly, [Fraction(1), Fraction(1)])
            val = _log(_mass_product(poly))
            if val < best:
                best, arg = val, m
        if best > theirs:
            failures.append(f"L={L}: (x+1)^m never ties Q=1, which m=0 must")
        if theirs - best > L:
            failures.append(f"L={L}: (x+1)^{arg} saves {theirs - best:.2f} > L")
        checks += 1
    return checks


#: Every check, in the order :func:`main` prints them.  ``test_masstwo.py``
#: runs each as its own test.
CHECKS = {
    "summed Jensen rows checked exactly": _check_rows,
    "rational Q beating the root product": _check_witness,
    "the (x+1)^m family saves only O(L)": _check_family,
}


def main() -> int:
    failures: list[str] = []
    for label, check in CHECKS.items():
        print(f"  {label:<43} : {check(failures)}")
    print()
    print(f"  {'L':>5} {'summed rows':>14} {'/L^2':>10} {'paper /L^2':>12} {'rows':>5}")
    for L in _ROW_L:
        prod, used = _row_sum(L)
        total = _log(prod)
        paper = _log(_paper_row_sum(L))
        print(
            f"  {L:>5} {total:>14.3f} {total / L**2:>10.6f} "
            f"{paper / L**2:>12.6f} {used:>5}"
        )
    print(f"  {'limit':>5} {'':>14} {0.06470684868:>10.6f}   (1/80 = 0.012500)")
    print()
    print(f"  {'L':>5} {'Lambda(PQ)':>12} {'Lambda(P)':>12} {'ratio':>8}  deg Q")
    for L, entry in _WITNESS.items():
        base = [Fraction(c) for c in _shifted(L)]
        q = [Fraction(c) for c in entry]
        mine = _log(_mass_product(_mul(base, q)))
        theirs = _log(_root_product_mass(L))
        ratio = mine / theirs
        print(f"  {L:>5} {mine:>12.4f} {theirs:>12.4f} {ratio:>8.4f}  {len(q) - 1}")
    if failures:
        for line in failures:
            print(f"  FAIL: {line}")
        return 1
    print()
    print("  rows give L^2/16 at L=97 but not 96; Q=1 is beaten")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
