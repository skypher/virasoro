#!/usr/bin/env python3
"""Test a fixed-charge recursion for the (Delta-lambda)^{-1} coefficient at
the second Jantzen layer of the torus one-point block (eta-reduced H_N).

Setting: minimal-model charge nu* = b*^2 = -p'/p, interior Kac weight
lambda = h_{r,s}(b*).  Everything is exact rational arithmetic at a fixed
rational external weight d (several values may be given).

Ground truth:
  * the confluence formula (paper.tex, Theorem 7.3): principal parts of
    H_N(c*, Delta, d) at every Kac weight as constant terms of collision
    moments, computed in the local coordinate u = nu - nu*;
  * optionally, direct Shapovalov inversion (tools/direct_reconstruction.py)
    for small N, as an independent check of the engine.

Candidate (to be tested), for N in the second layer:
  A_{lambda,1,N} = sum_{a in C_lambda} R_a(nu*) FP_{mu_a} H_{N-l_a}(c*,.)
      + sum_{pairs (a,g)} [ K_{ag} H_{M'}(c*, nu_ag) + M_{ag} dH_{M'}/dDelta(c*, nu_ag) ]
  where a runs over the labels at lambda, g over the labels whose pole sits at
  the shifted weight mu_a = z_a(nu*), nu_ag = z_g(nu*), M' = N - l_a - l_g,
  e_ag(u) = z_a(u) - h_g(u) = sigma u + tau u^2 + ..., P = R_a R_g = P0 + P1 u,
  K_{ag} = P1/sigma - P0 tau/sigma^2,  M_{ag} = P0 z_g'(nu*)/sigma.
  Only fixed-charge blocks H_M(c*, Delta) enter; derivatives in b of blocks
  drop out because sum_{(a,g)->nu} P0/sigma = 0 (checked).

Usage: python3 -u layer2_recursion.py --p 2 --pp 3 --r 1 --s 1 --nmax 9 \
           --d 3/7 --d -5/11 [--gram-max 7] [--prec 24]
       python3 -u layer2_recursion.py -h | --help   (print this usage and exit)
"""

import argparse
import sys
import time
from fractions import Fraction as Fr
from functools import lru_cache

T0 = time.time()


def log(msg):
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


# ------------------------------------------------------------------ series
# Truncated Laurent series in u: coefficients c[i] of u^(v+i), exact through
# absolute exponent p (an error term O(u^(p+1)) is implicit).

class Ser:
    __slots__ = ("v", "c", "p")

    def __init__(self, v, c, p):
        self.v, self.c, self.p = v, c, p
        self._norm()

    def _norm(self):
        k = 0
        while k < len(self.c) and self.c[k] == 0:
            k += 1
        if k:
            self.c = self.c[k:]
            self.v += k
        if self.v > self.p:
            self.c = []
            self.v = self.p + 1
        else:
            self.c = self.c[: self.p - self.v + 1]

    def is_zero_known(self):
        return not self.c

    def coef(self, e):
        if e > self.p:
            raise ArithmeticError(f"coefficient u^{e} unknown (precision {self.p})")
        i = e - self.v
        return self.c[i] if 0 <= i < len(self.c) else Fr(0)


def ser_const(x, prec):
    return Ser(0, [Fr(x)], prec)


def ser_poly(coeffs, prec):
    """Exact polynomial sum coeffs[i] u^i."""
    return Ser(0, [Fr(x) for x in coeffs], prec)


def ser_add(a, b):
    p = min(a.p, b.p)
    v = min(a.v, b.v)
    out = [Fr(0)] * max(0, p - v + 1)
    for s in (a, b):
        for i, x in enumerate(s.c):
            e = s.v + i
            if e <= p:
                out[e - v] += x
    return Ser(v, out, p)


def ser_scale(a, k):
    return Ser(a.v, [x * k for x in a.c], a.p)


def ser_mul(a, b):
    if not a.c or not b.c:
        # known-zero to given precision
        p = min(a.p + b.v, b.p + a.v)
        return Ser(p + 1, [], p)
    v = a.v + b.v
    p = min(a.p + b.v, b.p + a.v)
    n = p - v + 1
    out = [Fr(0)] * max(0, n)
    ac, bc = a.c, b.c
    for i, x in enumerate(ac):
        if i >= n:
            break
        lim = min(len(bc), n - i)
        for j in range(lim):
            out[i + j] += x * bc[j]
    return Ser(v, out, p)


def ser_inv(a):
    if not a.c:
        raise ZeroDivisionError("inverse of a series that is zero to known precision")
    v = a.v
    rel = a.p - v  # relative precision of the unit part
    c0 = a.c[0]
    out = []
    for k in range(rel + 1):
        s = Fr(1) if k == 0 else Fr(0)
        for j in range(1, min(k, len(a.c) - 1) + 1):
            s -= a.c[j] * out[k - j]
        out.append(s / c0)
    return Ser(-v, out, -v + rel)


def ser_sub(a, b):
    return ser_add(a, ser_scale(b, -1))


def ct(a):
    return a.coef(0)


# ------------------------------------------------------- model quantities

class Model:
    def __init__(self, p, pp, d, prec):
        self.p, self.pp = p, pp
        self.nu0 = Fr(-pp, p)
        self.d = Fr(d)
        self.prec = prec
        self.c0 = 13 + 6 * self.nu0 + 6 / self.nu0
        self._R = {}
        self._h = {}
        self._S = {}
        self._pp_cache = {}

    # polynomial in nu -> polynomial in u (nu = nu0 + u)
    def shift(self, coeffs):
        cur = [Fr(x) for x in coeffs]
        res = []
        while cur:
            q = [Fr(0)] * (len(cur) - 1)
            acc = cur[-1]
            for i in range(len(cur) - 2, -1, -1):
                q[i] = acc
                acc = cur[i] + acc * self.nu0
            res.append(acc)
            cur = q
        return res

    def nu_poly(self, coeffs):
        return ser_poly(self.shift(coeffs), self.prec)

    def h(self, r, s):
        key = (r, s)
        if key not in self._h:
            # ((nu+1)^2 - (r nu + s)^2) / (4 nu)
            num = [1 - s * s, 2 - 2 * r * s, 1 - r * r]
            self._h[key] = ser_mul(self.nu_poly(num), ser_inv(self.nu_poly([0, 4])))
        return self._h[key]

    def hstar(self, r, s):
        nu = self.nu0
        return ((nu + 1) ** 2 - (r * nu + s) ** 2) / (4 * nu)

    def z(self, r, s):
        return ser_add(self.h(r, s), ser_const(r * s, self.prec))

    def R(self, r, s):
        key = (r, s)
        if key in self._R:
            return self._R[key]
        d = self.d
        ser = ser_const(Fr(1, 2), self.prec)
        # nu^(2rs-1)
        nupow = ser_const(1, self.prec)
        nu = self.nu_poly([0, 1])
        for _ in range(2 * r * s - 1):
            nupow = ser_mul(nupow, nu)
        ser = ser_mul(ser, nupow)
        den = ser_const(1, self.prec)
        for m in range(1 - r, r + 1):
            for n in range(1 - s, s + 1):
                if (m, n) in ((0, 0), (r, s)):
                    continue
                den = ser_mul(den, self.nu_poly([n, m]))
        ser = ser_mul(ser, ser_inv(den))
        # torus norm N_{r,s}(b,d)
        num = ser_const(1, self.prec)
        nden = ser_const(1, self.prec)
        for k in range(1, 2 * r, 2):
            for l in range(1, 2 * s, 2):
                for sg in (1, -1):
                    # (nu+1)^2 - 4 d nu - (k nu + sg l)^2
                    c0 = 1 - l * l
                    c1 = 2 - 4 * d - 2 * k * sg * l
                    c2 = 1 - k * k
                    num = ser_mul(num, self.nu_poly([c0, c1, c2]))
                    nden = ser_mul(nden, self.nu_poly([0, 4]))
        ser = ser_mul(ser, ser_mul(num, ser_inv(nden)))
        self._R[key] = ser
        return ser

    def labels(self, nmax):
        return [(r, s) for r in range(1, nmax + 1) for s in range(1, nmax // r + 1)]

    def S(self, a, M):
        """Shifted Laurent block H_M at z_a(u), expanded in u."""
        key = (a, M)
        if key in self._S:
            return self._S[key]
        if M == 0:
            res = ser_const(1, self.prec)
        else:
            res = Ser(self.prec + 1, [], self.prec)
            za = self.z(*a)
            for g in self.labels(M):
                lg = g[0] * g[1]
                term = ser_mul(self.R(*g), ser_inv(ser_sub(za, self.h(*g))))
                term = ser_mul(term, self.S(g, M - lg))
                res = ser_add(res, term)
        self._S[key] = res
        return res

    def principal_parts(self, M, kmax=8):
        """dict lambda -> {k: A_{lambda,k,M}} for H_M(c*, Delta, d), M >= 1."""
        if M in self._pp_cache:
            return self._pp_cache[M]
        classes = {}
        for a in self.labels(M):
            classes.setdefault(self.hstar(*a), []).append(a)
        out = {}
        for lam, labs in classes.items():
            moments = {}
            base = {a: ser_mul(self.R(*a), self.S(a, M - a[0] * a[1])) for a in labs}
            delta = {a: ser_sub(self.h(*a), ser_const(lam, self.prec)) for a in labs}
            for k in range(1, kmax + 1):
                tot = Ser(self.prec + 1, [], self.prec)
                for a in labs:
                    term = base[a]
                    for _ in range(k - 1):
                        term = ser_mul(term, delta[a])
                    tot = ser_add(tot, term)
                val = ct(tot)
                if val != 0:
                    moments[k] = val
            # sanity: the full moments must be regular (no negative powers)
            out[lam] = moments
        self._pp_cache[M] = out
        return out

    # fixed-charge block H_M(c*, Delta) from its partial fractions
    def H_value(self, M, x, deriv=0, skip=None):
        if M == 0:
            return Fr(1) if deriv == 0 else Fr(0)
        tot = Fr(0)
        for lam, mom in self.principal_parts(M).items():
            if lam == skip:
                continue
            for k, A in mom.items():
                if lam == x:
                    raise ArithmeticError(f"H_{M} has a pole at {x}")
                if deriv == 0:
                    tot += A / (x - lam) ** k
                else:
                    tot += -k * A / (x - lam) ** (k + 1)
        return tot

    def H_FP(self, M, mu):
        """Finite part of H_M(c*, Delta) at Delta = mu (constant Laurent term)."""
        if M == 0:
            return Fr(1)
        # the group at mu is purely principal, so the finite part is the sum
        # of all other groups evaluated at mu
        return self.H_value(M, mu, skip=mu)


# ------------------------------------------------------------- candidate

def candidate(model, lam, N, report):
    """Fixed-charge candidate for A_{lambda,1,N}; also returns the top
    coefficient predicted from the same pairs and the cancellation sums."""
    first = Fr(0)
    Kpart = Fr(0)
    Mpart = Fr(0)
    top = Fr(0)
    cancel = {}
    flags = []
    for a in model.labels(N):
        if model.hstar(*a) != lam:
            continue
        la = a[0] * a[1]
        Ra = model.R(*a)
        if Ra.v < 0:
            flags.append(f"R{a} has a pole")
        Ra0 = Ra.coef(0)
        mu_a = model.hstar(*a) + la
        first += Ra0 * model.H_FP(N - la, mu_a)
        za = model.z(*a)
        ha = model.h(*a)
        for g in model.labels(N - la) if N - la >= 1 else []:
            lg = g[0] * g[1]
            if model.hstar(*g) != mu_a:
                continue
            Rg = model.R(*g)
            if Rg.v < 0:
                flags.append(f"R{g} has a pole")
            e = ser_sub(za, model.h(*g))
            if e.v != 1:
                flags.append(f"e{a}{g} has valuation {e.v}")
            sigma, tau = e.coef(1), e.coef(2)
            P = ser_mul(Ra, Rg)
            P0, P1 = P.coef(0), P.coef(1)
            nu_w = model.hstar(*g) + lg
            Mp = N - la - lg
            zg1 = model.z(*g).coef(1)
            ha1 = ha.coef(1)
            Hv = model.H_value(Mp, nu_w)
            Hd = model.H_value(Mp, nu_w, deriv=1)
            Kag = P1 / sigma - P0 * tau / sigma ** 2
            Mag = P0 * zg1 / sigma
            Kpart += Kag * Hv
            Mpart += Mag * Hd
            top += P0 * ha1 / sigma * Hv
            cancel[(nu_w, Mp)] = cancel.get((nu_w, Mp), Fr(0)) + P0 / sigma
            if report:
                log(f"    pair a={a} g={g}: nu={nu_w}, M'={Mp}, sigma={sigma}, "
                    f"P0/sigma*H={P0 / sigma * Hv}, M_ag/(P0 h_a'/sigma)="
                    f"{(Mag / (P0 * ha1 / sigma)) if ha1 != 0 else 'h_a const'}")
    return first, Kpart, Mpart, top, cancel, flags


# ------------------------------------------------------------------ gram

def gram_laurent(p, pp, d, lam, nmax, kmax=0):
    sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), ".."))
    import direct_reconstruction as dr
    nu0 = Fr(-pp, p)
    dr.C_CHARGE = 13 + 6 * nu0 + 6 / nu0
    dr.act.cache_clear()
    dr.set_external_weight(Fr(d))
    euler = dr.euler_coeffs(nmax)
    F = {0: {0: Fr(1)}}
    for N in range(1, nmax + 1):
        rf = dr.reconstruct_F(N, verbose=False)
        F[N] = rf.laurent_at(lam, kmax)
        log(f"  gram: F_{N} Laurent at {lam} done")
    H = {}
    for N in range(0, nmax + 1):
        acc = {}
        for j in range(N + 1):
            for k, v in F[N - j].items():
                acc[k] = acc.get(k, Fr(0)) + euler[j] * v
        H[N] = acc
    return H


# ------------------------------------------------------------------ main

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--pp", type=int, required=True)
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--s", type=int, required=True)
    ap.add_argument("--nmax", type=int, required=True)
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--d", action="append", required=True,
                    help="rational external weight; repeat for several values")
    ap.add_argument("--prec", type=int, default=24)
    ap.add_argument("--gram-max", type=int, default=0,
                    help="cross-check principal parts by Shapovalov inversion up to this N")
    ap.add_argument("--report-pairs", action="store_true")
    args = ap.parse_args()

    ok_all = True
    for dstr in args.d:
        d = Fr(dstr)
        m = Model(args.p, args.pp, d, args.prec)
        lam = m.hstar(args.r, args.s)
        log(f"model ({args.p},{args.pp}) c*={m.c0} lambda=h_({args.r},{args.s})={lam} d={d}")
        gram = gram_laurent(args.p, args.pp, d, lam, args.gram_max) if args.gram_max else {}
        for N in range(args.nmin, args.nmax + 1):
            pp = m.principal_parts(N)
            mom = pp.get(lam, {})
            A1, A2 = mom.get(1, Fr(0)), mom.get(2, Fr(0))
            higher = {k: v for k, v in mom.items() if k > 2}
            try:
                first, Kp, Mp, top, cancel, flags = candidate(m, lam, N, args.report_pairs)
            except ArithmeticError as exc:
                log(f"N={N:2d}: beyond the second layer ({exc}); higher poles "
                    f"{sorted(k for k in mom if k > 2)}")
                continue
            cand = first + Kp + Mp
            canc_ok = all(v == 0 for v in cancel.values())
            ok1 = cand == A1
            ok2 = top == A2
            line = (f"N={N:2d}: A2 {'=' if ok2 else '!='} pairs-top; "
                    f"A1 {'=' if ok1 else '!='} candidate; "
                    f"d_b-cancellation {'ok' if canc_ok else 'FAILS'}; "
                    f"higher poles {sorted(higher)}; flags {flags}")
            if N in gram:
                g = gram[N]
                gok = g.get(-1, Fr(0)) == A1 and g.get(-2, Fr(0)) == A2 and \
                    all(g.get(-k, Fr(0)) == 0 for k in range(3, 8))
                line += f"; gram {'agrees' if gok else 'DISAGREES'}"
                ok_all &= gok
            log(line)
            if not ok1:
                log(f"     A1={A1}  candidate={cand}  diff={A1 - cand}")
                log(f"     first={first} K={Kp} M={Mp}")
            ok_all &= ok1 and ok2 and canc_ok
    log("ALL OK" if ok_all else "SOME CHECK FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
