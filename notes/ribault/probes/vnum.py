"""Usage: python3 -u vnum.py [--L LMAX] [--seeds 1,2]
       python3 -u vnum.py -h | --help

Same recursion as vsym.py, in exact rationals at random (n0, n1, N0) (one run per seed); prints
mu_j(L) = j! v^(L-j)_j(lambda,mu) / z^j for both end nodes and flags any disagreement between seeds
or between the two end nodes (universality test).
"""
# py-rules-ok: case a, exact rationals, O(L^3) memoized values, seconds
import argparse
import random
from fractions import Fraction as Fr
from functools import lru_cache
from math import factorial


def run(n0, n1, N0, LMAX):
    def S(node):
        L, sg = node
        if L == 0:
            return Fr(n0)
        if L % 2 == 0:
            j = L // 2
            return Fr(n0 + j * N0 if sg == "+" else n0 - j * N0)
        j = (L - 1) // 2
        return Fr(n1 + j * N0 if sg == "+" else n1 - (j + 1) * N0)

    def layer_nodes(L):
        return [(0, "0")] if L == 0 else [(L, "+"), (L, "-")]

    def FS(a, b):
        out = []
        for L in range(a[0] + 1, b[0], 2):
            out += layer_nodes(L)
        if (b[0] - a[0]) % 2 == 1:
            out.append(b)
        return out

    def kappa_odd(a, c, b):
        num = (S(c) / S(a)) ** (b[0] - c[0])
        for cp in FS(c, b):
            num *= (S(cp) - S(a))
        den = Fr(1)
        fsac = set(FS(a, c))
        for ct in FS(a, b):
            if ct not in fsac:
                den *= (S(ct) - S(c))
        return num / den

    def kappa(a, nu, b):
        if (nu[0] - a[0]) % 2 == 1:
            return kappa_odd(a, nu, b)
        c = (a[0] + 1, "+")
        return kappa_odd(c, nu, b) * kappa_odd(a, c, b) / kappa_odd(a, c, nu)

    @lru_cache(maxsize=None)
    def v(a, b, k, j):
        if j == 0:
            return Fr(1)
        out = v(a, b, k + 1, j - 1)
        for nu in layer_nodes(a[0] + k):
            out -= kappa(a, nu, b) * v(nu, b, 1, j - 1)
        return out / j

    lam = (0, "0")
    res = {}
    for L in range(1, LMAX + 1):
        rows = []
        for mu in layer_nodes(L):
            z = S(mu) / S(lam)
            rows.append([factorial(j) * v(lam, mu, L - j, j) / z ** j for j in range(L)])
        res[L] = rows
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--L", type=int, default=12)
    ap.add_argument("--seeds", default="1,2")
    a = ap.parse_args()
    allres = []
    for sd in a.seeds.split(","):
        rnd = random.Random(int(sd))
        n0 = Fr(rnd.randint(1, 10**6), rnd.randint(1, 10**6))
        n1 = Fr(rnd.randint(1, 10**6), rnd.randint(1, 10**6))
        N0 = Fr(rnd.randint(1, 10**6), rnd.randint(1, 10**6))
        allres.append(run(n0, n1, N0, a.L))
    for L in range(1, a.L + 1):
        rows = [r for res in allres for r in res[L]]
        same = all(r == rows[0] for r in rows)
        print(f"L={L} universal={same} mu_j = {[str(x) for x in rows[0]]}", flush=True)


if __name__ == "__main__":
    main()
