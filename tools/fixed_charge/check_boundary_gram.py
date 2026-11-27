"""Usage: python3 -u check_boundary_gram.py [--p P --pp PP --x0 X0] [--d D] [--nmax N]
       python3 -u check_boundary_gram.py -h | --help

Theorem 18(iii) of notes/ribault/subleading.tex against direct Shapovalov inversion at c* (gram_laurent):
at the boundary weight lambda = d_{x0}, for every level N <= nmax the pole order of H_N(c*,.,d) at
lambda is the number D of nodes of level <= N (when H_{N-l_D}(c*,mu_D,d) != 0), and at N = l_D the
coefficient of (Delta-lambda)^-D is rho_g prod_{0<i<D}(h'_{lambda mu_D} - h'_{lambda mu_i}).
"""
# py-rules-ok: case a, Shapovalov inversion at one weight up to level nmax (8 at c = 0: seconds)
# stop-when: all levels printed
import argparse
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from layer2_recursion import Model, gram_laurent, ser_sub, ser_const  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, default=2)
    ap.add_argument("--pp", type=int, default=3)
    ap.add_argument("--x0", type=int, default=2)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--nmax", type=int, default=8)
    a = ap.parse_args()
    p, pp, x0 = a.p, a.pp, a.x0
    N0 = 2 * p * pp
    eps = 1 if x0 % p == 0 else -1
    T = [x0 + ((-1) ** k) * ((k + 1) // 2) * N0 for k in range(6)]
    dval = lambda x: Fr(x * x - (pp - p) ** 2, 4 * p * pp)  # noqa: E731
    lam = dval(x0)
    lev = [dval(abs(t)) - lam for t in T]
    model = Model(p, pp, Fr(a.d), 40)

    def label(ia, ib):
        sgn = 1 if T[ib] > 0 else -1
        xg = (-eps * sgn) * T[ia]
        B = abs(T[ib])
        return int(Fr(B + xg, 2 * pp)), int(Fr(B - xg, 2 * p))

    def hp(g):
        return ser_sub(model.h(*g), ser_const(model.hstar(*g), 40)).coef(1)

    G = gram_laurent(p, pp, Fr(a.d), lam, a.nmax, 0)
    ok = bad = 0
    for N in range(1, a.nmax + 1):
        D = max(k for k in range(len(T)) if lev[k] <= N)
        poles = [k for k, v in G[N].items() if k < 0 and v != 0]
        order = -min(poles) if poles else 0
        line = f"N={N}: nodes up to layer {D}, pole order {order}"
        good = order == D
        if N == lev[D] and D >= 1:
            g = label(0, D)
            R = model.R(*g)
            pred = R.coef(R.v)
            for i in range(1, D):
                pred *= hp(g) - hp(label(0, i))
            line += f", top {G[N].get(-D)} vs formula {pred}"
            good = good and G[N].get(-D) == pred
        ok += good
        bad += not good
        print(line + ("" if good else "  <-- differs"), flush=True)
    print(f"boundary weight x0={x0} of ({p},{pp}): {ok} levels agree, {bad} differ", flush=True)


if __name__ == "__main__":
    main()
