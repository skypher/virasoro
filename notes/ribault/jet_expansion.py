#!/usr/bin/env python3
"""Jet expansion of the confluence moments: which data at b != b* survive?

For the torus block (eta-reduced H_N) at a minimal-model charge nu* = -p'/p
and a Kac weight lambda, the confluence formula (paper.tex, Theorem 7.3)
writes A_{lambda,k,N} as the constant term in u = nu - nu* of collision
moments built from shifted blocks S_{a,M}(u) = H_M(nu* + u, z_a(u)).

Each shifted block is split at mu = z_a(nu*) into the colliding group at mu
(labels g with h_g(nu*) = mu, expanded recursively) and a remainder Reg that
is jointly regular at (nu*, mu).  The remainder is Taylor expanded in
(u, Delta - mu); its jets J[(M, mu), i, j] = d_u^i d_Delta^j Reg(nu*, mu)
are kept as formal unknowns.  Jets with i = 0 are fixed-charge data
(Laurent coefficients of H_M(c*, Delta) at mu); jets with i >= 1 are
derivatives in b and are not.

The script prints, for each N and k, the coefficients of the jets with
i >= 1 (all zero means a recursion in fixed-charge data exists in this
form), and checks that the fixed-charge part reproduces A_{lambda,k,N}.

Usage: python3 -u jet_expansion.py --p 2 --pp 3 --r 1 --s 1 --nmin 5 --nmax 14 \
           --d 3/7 [--jmax 6] [--prec 26] [--no-values]
       python3 -u jet_expansion.py -h | --help   (print this usage and exit)
"""

import argparse
import sys
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from layer2_recursion import (Model, Ser, ser_add, ser_const, ser_inv,  # noqa: E402
                              ser_mul, ser_sub, ct, log)


def jadd(A, B):
    out = dict(A)
    for k, s in B.items():
        out[k] = ser_add(out[k], s) if k in out else s
    return out


def jmul(A, s):
    return {k: ser_mul(v, s) for k, v in A.items()}


class Jets:
    def __init__(self, model, jmax):
        self.m = model
        self.jmax = jmax
        self.memo = {}

    def S(self, a, M):
        key = (a, M)
        if key in self.memo:
            return self.memo[key]
        m = self.m
        if M == 0:
            res = {("one",): ser_const(1, m.prec)}
        else:
            la = a[0] * a[1]
            mu = m.hstar(*a) + la
            za = m.z(*a)
            dz = ser_sub(za, ser_const(mu, m.prec))
            u = Ser(1, [Fr(1)], m.prec)
            res = {}
            upow = ser_const(1, m.prec)
            for i in range(self.jmax + 1):
                dzpow = ser_const(1, m.prec)
                for j in range(self.jmax + 1 - i):
                    coef = ser_mul(upow, dzpow)
                    coef = Ser(coef.v, [x / (factorial(i) * factorial(j)) for x in coef.c], coef.p)
                    res[(M, mu, i, j)] = coef
                    dzpow = ser_mul(dzpow, dz)
                upow = ser_mul(upow, u)
            for g in m.labels(M):
                if m.hstar(*g) != mu:
                    continue
                lg = g[0] * g[1]
                pref = ser_mul(m.R(*g), ser_inv(ser_sub(za, m.h(*g))))
                res = jadd(res, jmul(self.S(g, M - lg), pref))
        self.memo[key] = res
        return res

    def moment(self, lam, k, N):
        m = self.m
        tot = {}
        for a in m.labels(N):
            if m.hstar(*a) != lam:
                continue
            la = a[0] * a[1]
            pref = m.R(*a)
            delta = ser_sub(m.h(*a), ser_const(lam, m.prec))
            for _ in range(k - 1):
                pref = ser_mul(pref, delta)
            tot = jadd(tot, jmul(self.S(a, N - la), pref))
        self.last_polar = {key: s.v for key, s in tot.items()
                           if key[0] != "one" and key[2] == 0 and s.c and s.v < 0}
        return {key: ct(s) for key, s in tot.items()}


def cstar_jet(model, M, mu, j):
    """j! [ (Delta-mu)^j ] (H_M(c*, Delta) - principal part at mu)."""
    if M == 0:
        return Fr(1) if j == 0 else Fr(0)
    tot = Fr(0)
    for lam, mom in model.principal_parts(M).items():
        if lam == mu:
            continue
        for k, A in mom.items():
            # d^j/dDelta^j (Delta - lam)^(-k) at mu
            rising = 1
            for t in range(j):
                rising *= (k + t)
            tot += A * (-1) ** j * rising / (mu - lam) ** (k + j)
    return tot


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--s", type=int, required=True)
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--nmax", type=int, required=True)
    ap.add_argument("--kmax", type=int, default=4)
    ap.add_argument("--d", required=True)
    ap.add_argument("--jmax", type=int, default=6)
    ap.add_argument("--prec", type=int, default=26)
    ap.add_argument("--no-values", action="store_true",
                    help="only report the surviving b-derivative jets (skip the full check)")
    args = ap.parse_args()

    m = Model(args.p, args.pp, Fr(args.d), args.prec)
    lam = m.hstar(args.r, args.s)
    J = Jets(m, args.jmax)
    log(f"model ({args.p},{args.pp}) lambda={lam} d={args.d} jmax={args.jmax} prec={args.prec}")
    ok_all = True
    for N in range(args.nmin, args.nmax + 1):
        for k in range(1, args.kmax + 1):
            coeffs = J.moment(lam, k, N)
            noncstar = {key: v for key, v in coeffs.items()
                        if key[0] != "one" and key[2] >= 1 and v != 0}
            top_j = max((key[3] for key in coeffs if key[0] != "one" and coeffs[key] != 0),
                        default=-1)
            msg = f"N={N:2d} k={k}: surviving b-jets: "
            if noncstar:
                msg += ", ".join(f"d_u^{key[2]} d_D^{key[3]} H_{key[0]}@{key[1]}: {v}"
                                 for key, v in sorted(noncstar.items(), key=lambda kv: (kv[0][0], kv[0][2], kv[0][3])))
            else:
                msg += "none"
            nterms = sum(1 for v in coeffs.values() if v != 0)
            msg += f"  (nonzero terms {nterms}, max Delta-order used {top_j})"
            polar = J.last_polar
            msg += "; chain sums c_(mu,j) regular" if not polar else \
                f"; POLAR chain sums {sorted((k[1], k[3], v) for k, v in polar.items())}"
            if top_j >= args.jmax - 1:
                msg += "  WARNING: raise --jmax"
            if not args.no_values:
                truth = m.principal_parts(N).get(lam, {}).get(k, Fr(0))
                if noncstar:
                    msg += f"  [A={truth}]"
                else:
                    val = Fr(0)
                    for key, v in coeffs.items():
                        if v == 0:
                            continue
                        if key[0] == "one":
                            val += v
                        else:
                            val += v * cstar_jet(m, key[0], key[1], key[3])
                    good = val == truth
                    ok_all &= good
                    msg += f"  fixed-charge part {'=' if good else '!='} A"
            log(msg)
    log("DONE" + ("" if ok_all else " (a fixed-charge reconstruction failed)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
