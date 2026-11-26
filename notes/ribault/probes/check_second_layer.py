"""Usage: python3 -u check_second_layer.py [--models 2:3,2:5,...] [--d D[,D2]]
       python3 -u check_second_layer.py -h | --help

Exact check of Proposition (Second layer) in notes/ribault/subleading.tex: for every interior
weight and both branches,
  c^{(2)}_{lambda->mu^pm_2,0}(b*) = -+ (n0/n1) R_{r,s}(b*) R_{p+-r, p'-+s}(b*),
  c^{(1)}_{lambda->mu^pm_2,1}(b*) = +- (m^pm_2/n0) c^{(2)}_{lambda->mu^pm_2,0}(b*),
with the chain functions from the reviewed engine of notes/ribault/fixed_charge_recursion.py.
"""
# py-rules-ok: case a, six small models at levels <= 2pp', the engine took about 1 s per model
# stop-when: all checks are printed
import argparse
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--models", default="2:3,2:5,3:4,2:7,3:5,4:5")
    ap.add_argument("--d", default="3/7,1/5")
    a = ap.parse_args()
    ok = bad = 0
    for mstr in a.models.split(","):
        p, pp = map(int, mstr.split(":"))
        for dstr in a.d.split(","):
            model = Model(p, pp, Fr(dstr), 30)
            for r in range(1, p):
                for s in range(1, pp):
                    if pp * r + p * s >= p * pp:
                        continue
                    n0, n1 = pp * r - p * s, pp * r + p * s
                    lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
                    lev = {+1: p * pp + n0, -1: p * pp - n0}
                    ch = ChainFunctions(model, max(lev.values()), 2, 8)
                    tab = ch.table(lam)
                    for sg in (+1, -1):
                        mu = lam + lev[sg]
                        m = 2 * p * pp + sg * n0
                        g1 = (p + r, pp - s) if sg == 1 else (p - r, pp + s)
                        rho = model.R(r, s).coef(0) * model.R(*g1).coef(0)
                        top = tab.get((2, mu, 0), Fr(0))
                        sub = tab.get((1, mu, 1), Fr(0))
                        t1 = top == -sg * Fr(n0, n1) * rho
                        t2 = sub == sg * Fr(m, n0) * top
                        if t1 and t2:
                            ok += 1
                        else:
                            bad += 1
                            print(f"FAIL ({p},{pp}) d={dstr} (r,s)=({r},{s}) sign {sg}: top formula {t1}, ratio {t2}", flush=True)
    print(f"checked {ok + bad} cases: {ok} pass, {bad} fail", flush=True)


if __name__ == "__main__":
    main()
