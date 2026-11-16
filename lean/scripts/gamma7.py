"""Solve G0 v1 = -G1 x7 at level 7 (data from the Lean engine) and evaluate gamma_7.

Usage: python3 -u gamma7.py [-h|--help]
Reads runs/lean-check/data7b.log (G0 matrix, the jet of G(1/2+x) x7, x7) and prints a solution
v1 (as a word list) and gamma = x7.(G2 x7) + (G1 x7).v1.
"""
import sys
import re
from fractions import Fraction as F
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
txt = open('/home/yang/virasoro/runs/lean-check/data7b.log').read()
blocks = []
depth = 0
cur = ''
for ch in txt:
    if ch == '[':
        if depth == 0:
            cur = ''
        depth += 1
    if depth > 0:
        cur += ch
    if ch == ']':
        depth -= 1
        if depth == 0:
            blocks.append(cur)


def num(s):
    s = s.strip()
    if '/' in s:
        a, b = s.split('/')
        return F(int(a), int(b))
    return F(int(s))


words = [list(map(int, re.findall(r'\d+', w))) for w in re.findall(r'\[[\d, ]*\]', blocks[0][1:-1])]
rows = re.findall(r'\[([^\[\]]*)\]', blocks[1])
G0 = [[num(x) for x in r.split(',')] for r in rows]
trip = re.findall(r'\(([^()]*)\)', blocks[2])
jet = [[num(x) for x in t.split(',')] for t in trip]
x7pairs = re.findall(r'\(\[([\d, ]*)\], ([-\d/ ]+)\)', blocks[3])
x7 = {tuple(map(int, w.split(','))): num(v) for w, v in x7pairs}
n = len(words)
assert len(G0) == n and len(jet) == n
xv = [x7.get(tuple(w), F(0)) for w in words]
G1x = [j[1] for j in jet]
G2x = [j[2] for j in jet]
# solve G0 v = -G1x by Gaussian elimination (singular system; free variables set to 0)
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
print('rank G0 =', r, flush=True)
print('gamma =', gamma, flush=True)
print('v1 =', [(words[i], str(v1[i])) for i in range(n) if v1[i] != 0], flush=True)
