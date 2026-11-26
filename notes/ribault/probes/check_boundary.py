"""Usage: python3 -u check_boundary.py [--models 2:3,2:5,...] [--layers L] [--nmax-cap N] [--d D]
       python3 -u check_boundary.py -h | --help

Boundary weights lambda = d_{x0} of M(p,p') with x0 a positive multiple of p or of p' (not of pp'),
x0 < pp'.  The nodes are the weights of momenta M_k = |T_k|, T_k = x0 + pi_k N0, N0 = 2pp',
pi_k = (-1)^k ceil(k/2) (one node per layer k).  Checks against the chain-function engine:
 (a) every residue R_g of the label lambda -> mu_D has t-order exactly 1 - D;
 (b) Top(lambda -> mu_D) = rho_{lambda mu_D} prod_{0<i<D} (h'_{lambda mu_D} - h'_{lambda mu_i});
 (c) c^(D-j)_{a->mu,j}(b*) = (1/j!) (T_mu/T_a)^j prod_{i=1}^{j} (T_a - T_{nu_i})/(T_mu - T_{nu_i}) Top(a->mu),
     nu_i the node of layer L_mu - i, for bases a = lambda and a = mu_1.
"""
# py-rules-ok: case a, chain tables from two nodes per boundary weight, levels capped by --nmax-cap; seconds per weight
# stop-when: the summary line is printed
import argparse
import os
import sys
import time
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model, ser_sub, ser_const  # noqa: E402


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
        N0 = 2 * p * pp
        model = Model(p, pp, Fr(a.d), a.prec)
        xs = sorted({x for x in range(1, p * pp) if (x % p == 0) != (x % pp == 0)})
        for x0 in xs:
            t0 = time.time()
            T = [x0 + ((-1) ** k) * ((k + 1) // 2) * N0 for k in range(a.layers + 1)]
            dval = lambda x: Fr(x * x - (pp - p) ** 2, 4 * p * pp)  # noqa: E731
            lam = dval(x0)
            lev = [dval(abs(t)) - lam for t in T]
            K = [k for k in range(a.layers + 1) if lev[k] <= a.nmax_cap]
            if len(K) < 2:
                continue
            nmax = int(max(lev[k] for k in K))
            ch = ChainFunctions(model, nmax, a.layers, 8)

            def label(ia, ib):
                A, B = abs(T[ia]), abs(T[ib])
                sgn = 1 if T[ib] > 0 else -1
                xg = (-sgn if x0 % p == 0 else sgn) * T[ia]
                u, v = Fr(B + xg, 2 * pp), Fr(B - xg, 2 * p)
                assert u.denominator == 1 and v.denominator == 1 and u > 0 and v > 0 and abs(xg) == A
                return int(u), int(v)

            def hp(g):
                return ser_sub(model.h(*g), ser_const(model.hstar(*g), a.prec)).coef(1)

            for base in [0, 1]:
                if base not in K:
                    continue
                tab = ch.table(lam + lev[base])
                for mu in K:
                    D = mu - base
                    if D < 1:
                        continue
                    wmu = lam + lev[mu]
                    top = tab.get((D, wmu, 0), Fr(0))
                    if base == 0:
                        g = label(0, mu)
                        R = model.R(*g)
                        okv = R.v == 1 - D
                        pred = R.coef(R.v)
                        for i in range(1, D):
                            pred *= hp(g) - hp(label(0, i))
                        if okv and pred == top and top != 0:
                            ok += 1
                        else:
                            bad += 1
                            print(f"FAIL top ({p},{pp}) x0={x0} D={D}: order {R.v} top {top} pred {pred}", flush=True)
                    for j in range(1, D):
                        val = tab.get((D - j, wmu, j), Fr(0))
                        pred = Fr(T[mu], T[base]) ** j / factorial(j) * top
                        for i in range(1, j + 1):
                            pred *= Fr(T[base] - T[mu - i], T[mu] - T[mu - i])
                        if val == pred:
                            ok += 1
                        else:
                            bad += 1
                            print(f"FAIL kjD ({p},{pp}) x0={x0} base {base} mu {mu} j {j}: {val} vs {pred}", flush=True)
            print(f"({p},{pp}) x0={x0}: nodes {K}, levels {[str(lev[k]) for k in K]} [{time.time() - t0:.1f}s]", flush=True)
    print(f"checked {ok + bad} items: {ok} pass, {bad} fail", flush=True)


if __name__ == "__main__":
    main()
