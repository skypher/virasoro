"""LU certificates (with row permutation) for the eight B matrices of Lemma 8.4.

Usage: python3 -u luB.py OUT.lean [-h|--help]
Reads runs/lean-check/dataB.log.  For each label writes Lean definitions: the transpositions
whose product sigma satisfies B.submatrix sigma id = L * U, the lists of rows of L (lower
unitriangular) and U (upper triangular).  Every certificate is checked here in exact arithmetic.
"""
import sys
from fractions import Fraction as F
if len(sys.argv) < 2 or any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
sys.path.insert(0, '/home/yang/virasoro/runs/theta')
from detB import data, labels  # noqa: E402


def lu(B):
    n = len(B)
    A = [row[:] for row in B]
    perm = list(range(n))
    Lm = [[F(0)] * n for _ in range(n)]
    for col in range(n):
        p = next(i for i in range(col, n) if A[i][col] != 0)
        if p != col:
            A[col], A[p] = A[p], A[col]
            perm[col], perm[p] = perm[p], perm[col]
            Lm[col], Lm[p] = Lm[p], Lm[col]
        for i in range(col + 1, n):
            f = A[i][col] / A[col][col]
            Lm[i][col] = f
            if f:
                A[i] = [a - f * b for a, b in zip(A[i], A[col])]
    for i in range(n):
        Lm[i][i] = F(1)
    return perm, Lm, A


def swaps_of(perm):
    # find transpositions t1..tk with (t1 * ... * tk)(i) = perm[i]
    n = len(perm)
    cur = list(range(n))  # cur = t1*...*tj as a function
    sw = []
    # we build sigma = t1 * t2 * ... ; choose greedily on positions
    target = perm[:]
    # decompose target into transpositions: target = s1 * s2 * ... * sk
    work = target[:]
    for i in range(n):
        if work[i] != i:
            j = work.index(i)
            # work = work_new * swap(i, j)  <=>  work_new = work * swap(i,j)
            work[i], work[j] = work[j], work[i]
            sw.append((i, j))
    # now target = swap_k * ... * swap_1 applied in reverse: check
    sw = sw[::-1]

    def apply(i):
        for a, b in reversed(sw):
            if i == a:
                i = b
            elif i == b:
                i = a
        return i
    assert all(apply(i) == perm[i] for i in range(n)), 'swap decomposition'
    return sw


def q(x):
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


if __name__ == "__main__":
    out = []
    for (lab, D), B in zip(labels, data):
        n = len(B)
        perm, Lm, U = lu(B)
        # checks
        PB = [B[perm[i]] for i in range(n)]
        LU = [[sum(Lm[i][k] * U[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        assert PB == LU
        assert all(U[i][j] == 0 for i in range(n) for j in range(i))
        sw = swaps_of(perm)
        detU = F(1)
        for i in range(n):
            detU *= U[i][i]
        assert (-1) ** len(sw) * detU == D
        name = f"{lab[0]}{lab[1]}"
        out.append(f"-- label {lab}: {len(sw)} transpositions")
        out.append(f"def swaps_{name} : List (ℕ × ℕ) := {[(a, b) for a, b in sw]}".replace('[(', '[(').replace(')]', ')]'))
        out.append(f"def Lrows_{name} : List (List ℚ) := [" + ", ".join("[" + ", ".join(q(x) for x in row) + "]" for row in Lm) + "]")
        out.append(f"def Urows_{name} : List (List ℚ) := [" + ", ".join("[" + ", ".join(q(x) for x in row) + "]" for row in U) + "]")
        out.append("")
        print(lab, 'n', n, 'swaps', len(sw), 'ok', flush=True)
    open(sys.argv[1], 'w').write("\n".join(out))
