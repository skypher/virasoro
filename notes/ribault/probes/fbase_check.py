"""Usage: python3 -u fbase_check.py [--D DMAX] [--seed N]
       python3 -u fbase_check.py -h | --help

Check the closed form
   v^(D-j)_j(a,mu) = f_j(l_a, D)/j! * (S_mu/S_a)^j,
   f_{2i}(l,D) = (-1)^i C(n,i) C(l+n,i) / C(l+D-1,i),  n = floor((D-1)/2),
   f_{2i+1} = f_{2i} (D even), 0 (D odd),
for every base node a (both signs, layers 0..7) and end node mu with D = layer(mu) - layer(a) <= DMAX,
against the leading-order cutting recursion with the closed kappa (vnum.py), exact rationals at random
(n0, n1, N0).
"""
# py-rules-ok: case a, exact rationals, seconds
import argparse
import random
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb, factorial


def f(l, D, j):
    n = (D - 1) // 2
    if j % 2 == 1 and D % 2 == 1:
        return Fr(0)
    i = j // 2
    return Fr((-1) ** i * comb(n, i) * comb(l + n, i), comb(l + D - 1, i))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--D", type=int, default=9)
    ap.add_argument("--seed", type=int, default=7)
    a = ap.parse_args()
    rnd = random.Random(a.seed)
    n0, n1, N0 = (Fr(rnd.randint(1, 10**6), rnd.randint(1, 10**6)) for _ in range(3))

    def S(node):
        L, sg = node
        if L == 0:
            return n0
        if L % 2 == 0:
            j = L // 2
            return n0 + j * N0 if sg == "+" else n0 - j * N0
        j = (L - 1) // 2
        return n1 + j * N0 if sg == "+" else n1 - (j + 1) * N0

    def layer_nodes(L):
        return [(0, "0")] if L == 0 else [(L, "+"), (L, "-")]

    def FS(x, y):
        out = []
        for L in range(x[0] + 1, y[0], 2):
            out += layer_nodes(L)
        if (y[0] - x[0]) % 2 == 1:
            out.append(y)
        return out

    def kappa_odd(x, c, y):
        num = (S(c) / S(x)) ** (y[0] - c[0])
        for cp in FS(c, y):
            num *= (S(cp) - S(x))
        den = Fr(1)
        fs = set(FS(x, c))
        for ct in FS(x, y):
            if ct not in fs:
                den *= (S(ct) - S(c))
        return num / den

    def kappa(x, nu, y):
        if (nu[0] - x[0]) % 2 == 1:
            return kappa_odd(x, nu, y)
        c = (x[0] + 1, "+")
        return kappa_odd(c, nu, y) * kappa_odd(x, c, y) / kappa_odd(x, c, nu)

    @lru_cache(maxsize=None)
    def v(x, y, k, j):
        if j == 0:
            return Fr(1)
        out = v(x, y, k + 1, j - 1)
        for nu in layer_nodes(x[0] + k):
            out -= kappa(x, nu, y) * v(nu, y, 1, j - 1)
        return out / j

    ok = bad = 0
    for la in range(0, 8):
        for base in layer_nodes(la):
            for D in range(1, a.D + 1):
                for mu in layer_nodes(la + D):
                    z = S(mu) / S(base)
                    for j in range(D):
                        if v(base, mu, D - j, j) == f(la, D, j) / factorial(j) * z ** j:
                            ok += 1
                        else:
                            bad += 1
                            print(f"MISMATCH base {base} mu {mu} j {j}", flush=True)
    print(f"closed form for general bases: {ok} agree, {bad} disagree", flush=True)


if __name__ == "__main__":
    main()
