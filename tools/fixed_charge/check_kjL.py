"""Usage: python3 -u check_kjL.py [--models 2:3,2:5,...] [--layers L] [--nmax-cap N] [--d D]
       python3 -u check_kjL.py -h | --help

Exact check of the theorem on the coefficients with k + j = D in notes/ribault/subleading.tex against
the chain-function engine of tools/fixed_charge/fixed_charge_recursion.py: for every interior weight, every
base node a of layer <= 1 and end node mu (D = layer(mu) - layer(a) >= 1, level <= cap),
   c^(D-j)_{a->mu,j}(b*) = f_j(l_a, D)/j! (S_mu/S_a)^j c^(D)_{a->mu,0}(b*),
   f_{2i}(l,D) = (-1)^i C(n,i) C(l+n,i)/C(l+D-1,i), n = floor((D-1)/2),
   f_{2i+1} = f_{2i} (D even), 0 (D odd),
with S the signed momenta (S = n0 at lambda, S^+_{2j} = n0 + 2jpp', S^-_{2j} = n0 - 2jpp',
S^+_{2j+1} = n1 + 2jpp', S^-_{2j+1} = n1 - 2(j+1)pp').
"""
# py-rules-ok: case a, chain tables from a few nodes per weight, levels capped by --nmax-cap; seconds to minutes per model
# stop-when: the summary line is printed
import argparse
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model  # noqa: E402


def f(l, D, j):
    n = (D - 1) // 2
    if j % 2 == 1 and D % 2 == 1:
        return Fr(0)
    i = j // 2
    return Fr((-1) ** i * comb(n, i) * comb(l + n, i), comb(l + D - 1, i))


def nodes(p, pp, r, s, Lmax):
    """{(layer, sign): (level above lambda, signed momentum)}."""
    n0, n1, N0 = pp * r - p * s, pp * r + p * s, 2 * p * pp
    out = {(0, "0"): (0, n0)}
    for L in range(1, Lmax + 1):
        if L % 2 == 0:
            j = L // 2
            out[(L, "+")] = (j * (j * p * pp + n0), n0 + j * N0)
            out[(L, "-")] = (j * (j * p * pp - n0), n0 - j * N0)
        else:
            j = (L - 1) // 2
            out[(L, "+")] = ((r + j * p) * (s + j * pp), n1 + j * N0)
            out[(L, "-")] = (((j + 1) * p - r) * ((j + 1) * pp - s), n1 - (j + 1) * N0)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--models", default="2:3,2:5,3:4,2:7,3:5,4:5")
    ap.add_argument("--layers", type=int, default=4)
    ap.add_argument("--nmax-cap", type=int, default=40)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--prec", type=int, default=40)
    a = ap.parse_args()
    ok = bad = 0
    for mstr in a.models.split(","):
        p, pp = map(int, mstr.split(":"))
        model = Model(p, pp, Fr(a.d), a.prec)
        for r in range(1, p):
            for s in range(1, pp):
                if pp * r + p * s >= p * pp:
                    continue
                t0 = time.time()
                n0 = pp * r - p * s
                lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
                nd = {k: v for k, v in nodes(p, pp, r, s, a.layers).items() if v[0] <= a.nmax_cap}
                nmax = max(v[0] for v in nd.values())
                ch = ChainFunctions(model, nmax, a.layers, 8)
                w = {k: lam + v[0] for k, v in nd.items()}
                cnt = 0
                for base in [k for k in nd if k[0] <= 1]:
                    tab = ch.table(w[base])
                    for mu in nd:
                        D = mu[0] - base[0]
                        if D < 1 or w[mu] <= w[base]:
                            continue
                        top = tab.get((D, w[mu], 0), Fr(0))
                        z = Fr(nd[mu][1], nd[base][1])
                        for j in range(1, D):
                            val = tab.get((D - j, w[mu], j), Fr(0))
                            pred = f(base[0], D, j) / factorial(j) * z ** j * top
                            cnt += 1
                            if val == pred and top != 0:
                                ok += 1
                            else:
                                bad += 1
                                print(f"FAIL ({p},{pp}) (r,s)=({r},{s}) base {base} mu {mu} j {j}: {val} vs {pred}", flush=True)
                print(f"({p},{pp}) (r,s)=({r},{s}): {cnt} coefficients checked [{time.time() - t0:.1f}s]", flush=True)
    print(f"checked {ok + bad} coefficients: {ok} pass, {bad} fail", flush=True)


if __name__ == "__main__":
    main()
