"""Usage: python3 -u check_lower.py [--p P --pp PP --r R --s S] [--d D] [--nmax N]
       python3 -u check_lower.py -h | --help

Lower coefficients from data at c*.  For the interior weight lambda = h_{r,s}(b*) and every node mu of
level <= nmax, compute
   c^(k)_{lambda->mu,0}(b*)  =  [x^-k] H_{mu-lambda}(c*, lambda+x)
       - sum_{nu} sum_j c^(k)_{lambda->nu,j}(b*) * j! [y^j] H_{mu-nu}(c*, nu+y)
(nu over the nodes strictly between, levels from Shapovalov inversion at c*: gram_laurent), and compare
with the chain-function values of the engine.  Also prints c^(k)_{lambda->mu,0}(b*)/Top for k < D at two
values of d (the lower coefficients are not multiples of the top one).
"""
# py-rules-ok: case a, Shapovalov inversion at levels <= nmax (<= 7 at c = 0 takes seconds) and chain tables
# stop-when: all comparisons printed
import argparse
import os
import sys
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model, gram_laurent  # noqa: E402


def nodes(p, pp, r, s, Lmax):
    n0, n1 = pp * r - p * s, pp * r + p * s
    out = {(0, "0"): 0}
    for L in range(1, Lmax + 1):
        if L % 2 == 0:
            j = L // 2
            out[(L, "+")] = j * (j * p * pp + n0)
            out[(L, "-")] = j * (j * p * pp - n0)
        else:
            j = (L - 1) // 2
            out[(L, "+")] = (r + j * p) * (s + j * pp)
            out[(L, "-")] = ((j + 1) * p - r) * ((j + 1) * pp - s)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, default=2)
    ap.add_argument("--pp", type=int, default=3)
    ap.add_argument("--r", type=int, default=1)
    ap.add_argument("--s", type=int, default=1)
    ap.add_argument("--d", default="3/7,1/5")
    ap.add_argument("--nmax", type=int, default=7)
    a = ap.parse_args()
    p, pp, r, s = a.p, a.pp, a.r, a.s
    n0 = pp * r - p * s
    lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
    nd = {k: v for k, v in nodes(p, pp, r, s, 4).items() if v <= a.nmax}
    ok = bad = 0
    ratios = {}
    for dstr in a.d.split(","):
        d = Fr(dstr)
        model = Model(p, pp, d, 40)
        ch = ChainFunctions(model, a.nmax, 4, 8)
        tab = ch.table(lam)
        G = {k: gram_laurent(p, pp, d, lam + v, a.nmax, 6) for k, v in nd.items()}
        for mu, lev in nd.items():
            if mu[0] == 0:
                continue
            for k in range(1, mu[0] + 1):
                val = G[(0, "0")][lev].get(-k, Fr(0))
                for nu, lnu in nd.items():
                    if not (0 < lnu < lev):
                        continue
                    for j in range(0, 6):
                        cnu = tab.get((k, lam + lnu, j), Fr(0))
                        if cnu:
                            val -= cnu * factorial(j) * G[nu][lev - lnu].get(j, Fr(0))
                truth = tab.get((k, lam + lev, 0), Fr(0))
                if val == truth:
                    ok += 1
                else:
                    bad += 1
                    print(f"MISMATCH d={dstr} mu={mu} k={k}: c*-data {val} vs chains {truth}", flush=True)
                if k < mu[0]:
                    top = tab.get((mu[0], lam + lev, 0), Fr(0))
                    ratios.setdefault((mu, k), []).append(truth / top if top else None)
    for key, v in sorted(ratios.items()):
        print(f"c^({key[1]})_(lambda->{key[0]},0)(b*)/Top at d = {a.d}: {[str(x) for x in v]}", flush=True)
    print(f"({p},{pp}) (r,s)=({r},{s}): lower coefficients from Shapovalov data at c*: {ok} agree, {bad} disagree", flush=True)


if __name__ == "__main__":
    main()
