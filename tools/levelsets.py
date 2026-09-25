"""The level-set search reported after ``prop:gausslow`` in the complex paper.

For ``H`` in ``Z[y]`` with ``H(0) = 0``, positive leading coefficient,
coefficients in ``[-B, B]`` and degree at most ``s``, group the Gaussian ``y``
with ``|Re y| <= Y`` and ``1 <= Im y <= Y`` by the real value ``H(y)``; a group
is the set of prescribed roots of ``H(x) - v``.  Prints, per degree, the size of
the largest group and every group of size at least three.

    uv run --with numpy python tools/levelsets.py 2 7 40

The paper's ranges are ``(B, s, Y) = (1, 10, 30), (2, 7, 40), (3, 5, 50),
(5, 4, 60)``; every value stays far inside ``int64``.  A stdlib check on a
small range is ``test_one_heavy_coefficient`` in ``tests/test_complex.py``.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict

import numpy as np


def search(big_b: int, degree: int, box: int) -> None:
    pts = np.array(
        [(a, b) for a in range(-box, box + 1) for b in range(1, box + 1)],
        dtype=np.int64,
    )
    a, b = pts[:, 0], pts[:, 1]
    for s in range(1, degree + 1):
        largest, big = 0, []
        for h in itertools.product(range(-big_b, big_b + 1), repeat=s):
            if h[-1] <= 0:
                continue
            re = np.zeros(len(pts), dtype=np.int64)
            im = np.zeros(len(pts), dtype=np.int64)
            for c in reversed(h):
                re, im = (re + c) * a - im * b, (re + c) * b + im * a
            real = im == 0
            groups = defaultdict(list)
            for y, v in zip(pts[real].tolist(), re[real].tolist(), strict=True):
                groups[v].append(tuple(y))
            for v, ys in groups.items():
                largest = max(largest, len(ys))
                if len(ys) >= 3:
                    big.append((h, v, ys))
        print(s, largest, big, flush=True)


if __name__ == "__main__":
    search(*(int(arg) for arg in sys.argv[1:4]))
