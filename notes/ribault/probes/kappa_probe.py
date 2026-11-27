"""Usage: python3 -u kappa_probe.py --p P --pp PP [--d D] [--layers L] [--nmax-cap N] [--prec N]
       python3 -u kappa_probe.py -h | --help

Ratios of top coefficients in the braided diagram.  At an interior weight lambda = h_{r,s}(b*) of
M(p,p'), the nodes of layer i are lambda + l^pm_i, with signed momenta m^pm_i (Section 8 of
paper.tex; layer 0 is lambda with momentum n0).  For nodes a above b (relative layer
L_ab = layer(b) - layer(a)) put Top(a->b) = c^{(L_ab)}_{a->b,0}(b*), the leading chain-function value
(N/gamma of Theorem 8.2 when a = lambda).  Print
   kappa(lambda, nu, mu) = Top(lambda->nu) Top(nu->mu) / Top(lambda->mu)
for every node nu strictly between lambda and mu, with the momenta, and check the leading-order
cutting recursion  j c^{(k)}_{lambda->mu,j} = c^{(k+1)}_{lambda->mu,j-1}
   - sum_{nu in layer k} c^{(k)}_{lambda->nu,0} c^{(1)}_{nu->mu,j-1}   (k + j = L).
"""
# py-rules-ok: case a, chain-function tables from a handful of nodes with the existing series engine, levels capped by --nmax-cap
# stop-when: the tables for the requested model are printed
import argparse
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "..", "..", "tools", "fixed_charge"))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model  # noqa: E402


def interior_labels(p, pp):
    return [(r, s) for r in range(1, p) for s in range(1, pp) if pp * r + p * s < p * pp]


def nodes(p, pp, r, s, Lmax):
    """{(layer, sign): (level above lambda, signed momentum)}; layer 0 = lambda."""
    n0, n1 = pp * r - p * s, pp * r + p * s
    out = {(0, "0"): (0, n0)}
    for L in range(1, Lmax + 1):
        if L % 2 == 0:
            j = L // 2
            out[(L, "+")] = (j * (j * p * pp + n0), 2 * j * p * pp + n0)
            out[(L, "-")] = (j * (j * p * pp - n0), 2 * j * p * pp - n0)
        else:
            j = (L - 1) // 2
            out[(L, "+")] = ((r + j * p) * (s + j * pp), 2 * j * p * pp + n1)
            out[(L, "-")] = (((j + 1) * p - r) * ((j + 1) * pp - s), 2 * (j + 1) * p * pp - n1)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--layers", type=int, default=3)
    ap.add_argument("--nmax-cap", type=int, default=30)
    ap.add_argument("--prec", type=int, default=40)
    a = ap.parse_args()
    p, pp = a.p, a.pp
    for (r, s) in interior_labels(p, pp):
        t0 = time.time()
        n0 = pp * r - p * s
        lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
        nd = {k: v for k, v in nodes(p, pp, r, s, a.layers).items() if v[0] <= a.nmax_cap}
        if len(nd) < 3:
            continue
        nmax = max(v[0] for v in nd.values())
        model = Model(p, pp, Fr(a.d), a.prec)
        ch = ChainFunctions(model, nmax, a.layers, 8)
        w = {k: lam + v[0] for k, v in nd.items()}
        tabs = {k: ch.table(w[k]) for k in nd}

        def val(a_, b_, k, j):
            return tabs[a_].get((k, w[b_], j), Fr(0))

        def top(a_, b_):
            return val(a_, b_, b_[0] - a_[0], 0)
        print(f"({p},{pp}) (r,s)=({r},{s}) n0={n0} momenta " +
              ", ".join(f"{k[0]}{k[1]}:{v[1]}" for k, v in sorted(nd.items())) + f" [{time.time() - t0:.1f}s]", flush=True)
        lam_key = (0, "0")
        for mu in sorted(nd):
            if mu[0] < 2:
                continue
            T = top(lam_key, mu)
            if T == 0:
                print(f"  mu={mu}: Top=0", flush=True)
                continue
            for nu in sorted(nd):
                if not (0 < nu[0] < mu[0]):
                    continue
                if w[nu] >= w[mu] or (w[mu] - w[nu]).denominator != 1:
                    continue
                kap = top(lam_key, nu) * top(nu, mu) / T
                print(f"  kappa(lambda, {nu[0]}{nu[1]} [m={nd[nu][1]}], {mu[0]}{mu[1]} [m={nd[mu][1]}]) = {kap}", flush=True)
            # leading-order cutting recursion
            L = mu[0]
            for k in range(1, L):
                j = L - k
                lhs = j * val(lam_key, mu, k, j)
                rhs = val(lam_key, mu, k + 1, j - 1)
                for nu in nd:
                    if nu[0] == k and w[nu] < w[mu]:
                        rhs -= val(lam_key, nu, k, 0) * val(nu, mu, 1, j - 1)
                print(f"  cutting at leading order, mu={mu}, k={k}, j={j}: {'OK' if lhs == rhs else 'FAILS'}", flush=True)


if __name__ == "__main__":
    main()
