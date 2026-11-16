"""Normalized singular vectors psi8 in M(1/2,33/16) and psi6 in M(1/2,65/16): solve B p = e_last.

Usage: python3 -u psi.py [-h|--help]
Uses the B matrices of runs/lean-check/dataB.log (columns in lexWords order) and prints the
coefficient lists as Lean literals.
"""
import sys
from fractions import Fraction as F
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
sys.path.insert(0, '/home/yang/virasoro/runs/theta')
from detB import data, labels  # noqa: E402

W8 = [[8], [7, 1], [6, 2], [6, 1, 1], [5, 3], [5, 2, 1], [5, 1, 1, 1], [4, 4], [4, 3, 1],
      [4, 2, 2], [4, 2, 1, 1], [4, 1, 1, 1, 1], [3, 3, 2], [3, 3, 1, 1], [3, 2, 2, 1],
      [3, 2, 1, 1, 1], [3, 1, 1, 1, 1, 1], [2, 2, 2, 2], [2, 2, 2, 1, 1], [2, 2, 1, 1, 1, 1],
      [2, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]
W6 = [[6], [5, 1], [4, 2], [4, 1, 1], [3, 3], [3, 2, 1], [3, 1, 1, 1], [2, 2, 2], [2, 2, 1, 1],
      [2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]]


def solve(B, rhs):
    n = len(B)
    A = [row[:] + [rhs[i]] for i, row in enumerate(B)]
    for col in range(n):
        p = next(i for i in range(col, n) if A[i][col] != 0)
        A[col], A[p] = A[p], A[col]
        inv = 1 / A[col][col]
        A[col] = [x * inv for x in A[col]]
        for i in range(n):
            if i != col and A[i][col] != 0:
                f = A[i][col]
                A[i] = [a - f * b for a, b in zip(A[i], A[col])]
    return [A[i][n] for i in range(n)]


def q(x):
    return f"{x.numerator} / {x.denominator}" if x.denominator != 1 else f"{x.numerator}"


for lab, W in [((4, 2), W8), ((1, 6), W6)]:
    B = data[[l for l, _ in labels].index(lab)]
    n = len(B)
    e = [F(0)] * n
    e[-1] = F(1)
    p = solve(B, e)
    lit = "[" + ", ".join(f"({w}, {q(c)})" for w, c in zip(W, p) if c != 0) + "]"
    print(lab, 'nonzero', sum(1 for c in p if c != 0), flush=True)
    print(lit, flush=True)
