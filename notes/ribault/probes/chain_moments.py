"""Usage: python3 -u chain_moments.py --p P --pp PP [--d D] [--layers 2,3] [--nmax-cap N] [--prec N]
       python3 -u chain_moments.py -h | --help

Chain-by-chain data behind the fixed-charge coefficients with k + j = L (L = Jantzen layer of the
end point).  At an interior weight lambda = h_{r,s}(b*) of M(p,p') and an end point
mu = lambda + l^pm_L, enumerate every chain (g_0, ..., g_n) from lambda to mu (Definition 7.9 of
paper.tex), compute P_gamma = R_{g_0} prod_i R_{g_i}/(delta_{g_{i-1}} - delta_{g_i}) as a Laurent
series in u = b^2 - b*^2, and print its pole order, its leading coefficient w_gamma, and the
signed momenta
   Y_gamma = x_0 y_0 / n0,   X_gamma = x_n y_n / m,
where a label (u,v) has x = p'u - pv (momentum of its weight) and y = p'u + pv (momentum of its end),
n0 = p'r - ps and m is the signed momentum of mu.  Then print the moments
   S(a,b) = sum over chains of maximal pole order of w Y^a X^b   (a + b <= L - 1)
and the leading-order prediction for c^{(k)}_{lambda->mu,j}(b*)/c^{(L)}_{lambda->mu,0}(b*).
"""
# py-rules-ok: case a, chain enumeration at levels <= --nmax-cap with the existing series engine; second- and third-layer probes took seconds per model
# stop-when: the tables for the requested models are printed
import argparse
import os
import sys
import time
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from layer2_recursion import Model, ser_const, ser_inv, ser_mul, ser_sub  # noqa: E402


def interior_labels(p, pp):
    return [(r, s) for r in range(1, p) for s in range(1, pp) if pp * r + p * s < p * pp]


def layer_data(p, pp, r, s, L):
    n0, n1 = pp * r - p * s, pp * r + p * s
    if L % 2 == 0:
        j = L // 2
        return {"+": (j * (j * p * pp + n0), 2 * j * p * pp + n0), "-": (j * (j * p * pp - n0), 2 * j * p * pp - n0)}
    j = (L - 1) // 2
    return {"+": ((r + j * p) * (s + j * pp), 2 * j * p * pp + n1),
            "-": (((j + 1) * p - r) * ((j + 1) * pp - s), 2 * (j + 1) * p * pp - n1)}


def chains(model, lam, total, labels):
    """All chains from weight lam of total level `total` (lists of labels)."""
    out = []

    def rec(w, rem, acc):
        for g in labels:
            if model.hstar(*g) != w:
                continue
            l = g[0] * g[1]
            if l > rem:
                continue
            if l == rem:
                out.append(acc + [g])
            else:
                rec(w + l, rem - l, acc + [g])
    rec(lam, total, [])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--d", default="3/7")
    ap.add_argument("--layers", default="2,3")
    ap.add_argument("--nmax-cap", type=int, default=30)
    ap.add_argument("--prec", type=int, default=40)
    a = ap.parse_args()
    p, pp = a.p, a.pp
    model = Model(p, pp, Fr(a.d), a.prec)
    for (r, s) in interior_labels(p, pp):
        n0 = pp * r - p * s
        lam = Fr(n0 ** 2 - (pp - p) ** 2, 4 * p * pp)
        for L in [int(x) for x in a.layers.split(",")]:
            for sign, (lev, m) in sorted(layer_data(p, pp, r, s, L).items(), key=lambda kv: kv[1][0]):
                if lev > a.nmax_cap:
                    continue
                t0 = time.time()
                labels = model.labels(lev)
                data = []
                for ch in chains(model, lam, lev, labels):
                    P = model.R(*ch[0])
                    deltas = [ser_sub(model.h(*g), ser_const(model.hstar(*g), a.prec)) for g in ch]
                    for i in range(1, len(ch)):
                        P = ser_mul(P, ser_mul(model.R(*ch[i]), ser_inv(ser_sub(deltas[i - 1], deltas[i]))))
                    v = P.v if P.c else None
                    w = P.coef(P.v) if P.c else Fr(0)
                    (u0, v0), (un, vn) = ch[0], ch[-1]
                    x0, y0 = pp * u0 - p * v0, pp * u0 + p * v0
                    xn, yn = pp * un - p * vn, pp * un + p * vn
                    hp0 = deltas[0].coef(1) if deltas[0].v <= 1 else Fr(0)
                    hpn = deltas[-1].coef(1) if deltas[-1].v <= 1 else Fr(0)
                    data.append((ch, v, w, Fr(x0 * y0, n0), Fr(xn * yn, m), hp0, hpn))
                vmin = min(d[1] for d in data if d[1] is not None)
                print(f"({p},{pp}) (r,s)=({r},{s}) n0={n0} layer {L}{sign} level {lev} m={m}: {len(data)} chains, "
                      f"max pole order {-vmin} [{time.time() - t0:.1f}s]", flush=True)
                for ch, v, w, Y, X, _, _ in data:
                    print(f"    chain {ch}: order {v} Y={Y} X={X}" + (f" w={w}" if v == vmin else ""), flush=True)
                mx = [d for d in data if d[1] == vmin]
                S = {(i, j): sum(d[2] * d[3] ** i * d[4] ** j for d in mx) for i in range(L) for j in range(L - i)}
                low = {k: v for k, v in S.items() if sum(k) <= L - 2}
                top = {k: v for k, v in S.items() if sum(k) == L - 1}
                print(f"    moments a+b<=L-2 (should vanish if pole order = L-1): {low}", flush=True)
                tL = top[(L - 1, 0)]
                if tL != 0:
                    pred = {f"c{L - i}{j}": Fr((-m) ** j * (-n0) ** (L - 1 - j), (-n0) ** (L - 1)) * top[(L - 1 - j, j)] / tL / factorial(j)
                            for (i, j) in [(L - 1 - jj, jj) for jj in range(L)]}
                    print(f"    leading-order prediction c^(k)_j / top for k + j = L: {pred}", flush=True)


if __name__ == "__main__":
    main()
