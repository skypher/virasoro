"""Usage: python3 -u subleading_probe.py --p P --pp PP --d D[,D2,...] [--prec N] [--jmax J]
       python3 -u subleading_probe.py -h | --help

Probe: are the subleading fixed-charge coefficients module data?  At an interior weight
lambda = h_{r,s}(b*) of M(p,p'), for each second-layer end point mu = lambda + l^pm_2, print
  top = c^{(2)}_{lambda->mu,0}(b*)   (the double-pole coefficient N/gamma, Theorem 8.2),
  sub = c^{(1)}_{lambda->mu,1}(b*)   (coefficient of d/dDelta H_{N-l}(c*,mu) in A_{lambda,1,N}),
their ratio, and the Coulomb momentum m of mu (mu = (m^2-(p'-p)^2)/(4pp')).  The c = 0 case
(p,p') = (2,3), lambda = 0, mu = 5 gave ratio -11 = -m by hand.  Several external weights d test
whether the ratio depends on d.  Uses the reviewed engine of notes/ribault/fixed_charge_recursion.py.
"""
# py-rules-ok: case a, a few chain-function tables at levels <= 17 with the existing series engine, seconds to a minute per model (timed on the first slice)
# stop-when: the table for the requested models is printed
import argparse
import math
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "..", "..", "tools", "fixed_charge"))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model  # noqa: E402


def interior_labels(p, pp):
    out = []
    for r in range(1, p):
        for s in range(1, pp):
            if pp * r + p * s < p * pp:
                out.append((r, s))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--prec", type=int, default=30)
    ap.add_argument("--jmax", type=int, default=8)
    a = ap.parse_args()
    p, pp = a.p, a.pp
    for dstr in a.d.split(","):
        d = Fr(dstr)
        for (r, s) in interior_labels(p, pp):
            n0 = pp * r - p * s
            lam = Fr((pp * r - p * s) ** 2 - (pp - p) ** 2, 4 * p * pp)
            levels = {"+": p * pp + n0, "-": p * pp - n0}
            nmax = max(levels.values())
            t0 = time.time()
            model = Model(p, pp, d, a.prec)
            ch = ChainFunctions(model, nmax, 2, a.jmax)
            tab = ch.table(lam)
            for sign, l in sorted(levels.items(), key=lambda kv: kv[1]):
                mu = lam + l
                m2 = 4 * p * pp * mu + (pp - p) ** 2
                m = math.isqrt(int(m2)) if m2.denominator == 1 else None
                top = tab.get((2, mu, 0), Fr(0))
                sub = tab.get((1, mu, 1), Fr(0))
                ratio = (sub / top) if top != 0 else None
                print(f"(p,p')=({p},{pp}) d={d} (r,s)=({r},{s}) lambda={lam} branch {sign} level {l} mu={mu} "
                      f"m={m}: top={top} sub={sub} ratio={ratio} [{time.time() - t0:.1f}s]", flush=True)


if __name__ == "__main__":
    main()
