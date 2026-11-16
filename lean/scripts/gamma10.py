"""Solve G0 v1 = -G1 x10 at level 10 (data from the Lean engine) and evaluate gamma_10.

Usage: python3 -u gamma10.py [-h|--help]
Reads runs/lean-check/data10b.log: x10, decWords 10, the 42x42 matrix G0 at h = 1/16 and the
jet of G(1/16+x) x10.  Prints a solution v1 as a Lean literal and gamma.
"""
import sys
import re
from fractions import Fraction as F
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
lines = open('/home/yang/virasoro/runs/lean-check/data10b.log').read().split('\n')
iw = lines.index('WORDS')
ig = lines.index('G0')
ij = lines.index('JET')
ix = lines.index('X10')


def num(s):
    s = s.strip()
    if '/' in s:
        a, b = s.split('/')
        return F(int(a), int(b))
    return F(int(s))


words = [list(map(int, re.findall(r'\d+', l))) for l in lines[iw + 1:ig]]
G0 = [[num(x) for x in l.split(',')] for l in lines[ig + 1:ij]]
jet = [[num(x) for x in l.split(',')] for l in lines[ij + 1:ix]]
x10 = {}
for l in lines[ix + 1:]:
    if ';' in l:
        w, v = l.split(';')
        x10[tuple(map(int, re.findall(r'\d+', w)))] = num(v)
n = len(words)
assert len(G0) == n and len(jet) == n and n == 42, (len(G0), len(jet), n)
assert all(j[0] == 0 for j in jet), 'G0 x10 != 0'
xv = [x10.get(tuple(w), F(0)) for w in words]
G1x = [j[1] for j in jet]
G2x = [j[2] for j in jet]
A = [row[:] + [-G1x[i]] for i, row in enumerate(G0)]
piv = []
r = 0
for col in range(n):
    p = next((i for i in range(r, n) if A[i][col] != 0), None)
    if p is None:
        continue
    A[r], A[p] = A[p], A[r]
    inv = 1 / A[r][col]
    A[r] = [x * inv for x in A[r]]
    for i in range(n):
        if i != r and A[i][col] != 0:
            f = A[i][col]
            A[i] = [a - f * b for a, b in zip(A[i], A[r])]
    piv.append(col)
    r += 1
for i in range(r, n):
    assert A[i][n] == 0, 'inconsistent'
v1 = [F(0)] * n
for i, col in enumerate(piv):
    v1[col] = A[i][n]
for i in range(n):
    assert sum(G0[i][j] * v1[j] for j in range(n)) == -G1x[i]
gamma = sum(xv[i] * G2x[i] for i in range(n)) + sum(G1x[i] * v1[i] for i in range(n))


def q(x):
    return f"{x.numerator} / {x.denominator}" if x.denominator != 1 else f"{x.numerator}"


print('rank G0 =', r, flush=True)
print('gamma =', gamma, 'expected', F(-1121229484375, 192), gamma == F(-1121229484375, 192), flush=True)
print("[" + ", ".join(f"({words[i]}, {q(v1[i])})" for i in range(n) if v1[i] != 0) + "]", flush=True)
