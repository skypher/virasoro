"""Determinants of the eight B matrices of Lemma 8.4 (data from the Lean engine) and LU checks.

Usage: python3 -u detB.py [-h|--help]
Reads runs/lean-check/dataB.log, prints det B for each label, compares with the paper's table,
and reports whether Gaussian elimination needs row exchanges.
"""
import sys
from fractions import Fraction as F
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
txt = open('/home/yang/virasoro/runs/lean-check/dataB.log').read()
txt = txt.replace('\n', ' ')


def parse(s, i):
    # parse nested lists of rationals starting at s[i] == '['
    assert s[i] == '['
    i += 1
    out = []
    while True:
        while s[i] in ' ,':
            i += 1
        if s[i] == ']':
            return out, i + 1
        if s[i] == '[':
            v, i = parse(s, i)
            out.append(v)
        else:
            j = i
            while s[j] not in ',]':
                j += 1
            tok = s[i:j].strip()
            if '/' in tok:
                a, b = tok.split('/')
                out.append(F(int(a), int(b)))
            else:
                out.append(F(int(tok)))
            i = j


data, _ = parse(txt, txt.index('['))
labels = [((2, 1), F(3)), ((1, 3), F(12)), ((1, 2), F(3)), ((2, 2), F(-675, 2)),
          ((1, 5), F(91350)), ((4, 1), F(-2730)), ((4, 2), F(-17116376343198212705625, 32)),
          ((1, 6), F(505194765075, 32))]
if __name__ == "__main__":
  for (lab, Dpaper), B in zip(labels, data):
      n = len(B)
      A = [row[:] for row in B]
      det = F(1)
      swaps = 0
      for col in range(n):
          p = next((i for i in range(col, n) if A[i][col] != 0), None)
          if p is None:
              det = F(0)
              break
          if p != col:
              A[col], A[p] = A[p], A[col]
              det = -det
              swaps += 1
          det *= A[col][col]
          for i in range(col + 1, n):
              f = A[i][col] / A[col][col]
              if f:
                  A[i] = [a - f * b for a, b in zip(A[i], A[col])]
      print(lab, 'n =', n, 'det =', det, 'paper =', Dpaper, 'match =', det == Dpaper,
            'row swaps =', swaps, flush=True)
