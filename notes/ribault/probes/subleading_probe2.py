"""Usage: python3 -u subleading_probe2.py --p P --pp PP --d D[,D2,...] [--layers 2,3] [--nmax-cap N] [--prec N]
       python3 -u subleading_probe2.py -h | --help

Probe, second and third Jantzen layers.  At an interior weight lambda = h_{r,s}(b*) of M(p,p'),
for each end point mu = lambda + l^pm_L of layer L, print every nonzero chain-function value
c^{(k)}_{lambda->mu,j}(b*) with k <= L, j <= 3, as a ratio to the top value c^{(L)}_{lambda->mu,0}(b*)
(the pole-order-L coefficient N/gamma of Theorem 8.2), together with the signed momenta
n0 = p'r - ps of lambda and m^pm_L of mu (Section 8 of paper.tex).  End points with level above
--nmax-cap are skipped.  Uses the reviewed engine of notes/ribault/fixed_charge_recursion.py.
"""
# py-rules-ok: case a, chain-function tables with the existing series engine; levels capped by --nmax-cap, timed per model (second layer took about 1 s per model)
# stop-when: the tables for the requested models are printed
import argparse
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from fixed_charge_recursion import ChainFunctions  # noqa: E402
from layer2_recursion import Model  # noqa: E402


def interior_labels(p, pp):
    return [(r, s) for r in range(1, p) for s in range(1, pp) if pp * r + p * s < p * pp]


def layer_data(p, pp, r, s, L):
    """(level, signed momentum) of the two end points of layer L, keyed by sign."""
    n0, n1 = pp * r - p * s, pp * r + p * s
    if L % 2 == 0:
        j = L // 2
        return {"+": (j * (j * p * pp + n0), 2 * j * p * pp + n0), "-": (j * (j * p * pp - n0), 2 * j * p * pp - n0)}
    j = (L - 1) // 2
    return {"+": ((r + j * p) * (s + j * pp), 2 * j * p * pp + n1),
            "-": (((j + 1) * p - r) * ((j + 1) * pp - s), 2 * (j + 1) * p * pp - n1)}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--layers", default="2,3")
    ap.add_argument("--nmax-cap", type=int, default=30)
    ap.add_argument("--prec", type=int, default=40)
    ap.add_argument("--jmax", type=int, default=8)
    a = ap.parse_args()
    p, pp = a.p, a.pp
    layers = [int(x) for x in a.layers.split(",")]
    for dstr in a.d.split(","):
        d = Fr(dstr)
        for (r, s) in interior_labels(p, pp):
            n0 = pp * r - p * s
            lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
            ends = []
            for L in layers:
                for sign, (lev, m) in layer_data(p, pp, r, s, L).items():
                    if lev <= a.nmax_cap:
                        ends.append((L, sign, lev, m))
            if not ends:
                continue
            nmax = max(e[2] for e in ends)
            t0 = time.time()
            model = Model(p, pp, d, a.prec)
            ch = ChainFunctions(model, nmax, max(layers), a.jmax)
            tab = ch.table(lam)
            for (L, sign, lev, m) in sorted(ends, key=lambda e: e[2]):
                mu = lam + lev
                top = tab.get((L, mu, 0), Fr(0))
                vals = {(k, j): tab.get((k, mu, j), Fr(0)) for k in range(1, L + 1) for j in range(0, 4)}
                if top == 0:
                    nz = [kj for kj, v in vals.items() if v != 0]
                    print(f"({p},{pp}) d={d} (r,s)=({r},{s}) n0={n0} layer {L}{sign} level {lev} m={m}: top=0, nonzero={nz} [{time.time() - t0:.1f}s]", flush=True)
                    continue
                rat = " ".join(f"c{k}{j}={v / top}" for (k, j), v in sorted(vals.items()) if v != 0 and (k, j) != (L, 0))
                print(f"({p},{pp}) d={d} (r,s)=({r},{s}) n0={n0} layer {L}{sign} level {lev} m={m}: {rat} [{time.time() - t0:.1f}s]", flush=True)


if __name__ == "__main__":
    main()
