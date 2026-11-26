#!/usr/bin/env python3
"""Fixed-charge recursion at a fixed b* (any b*^2, rational or not).

Implements the recursion of notes/ribault/fixed_charge_recursion.tex:

  A_{lam,k,N} = sum_{mu} sum_{j>=0} c^{(k)}_{lam->mu,j}(b*) *
                d^j/dDelta^j [ H_{N-(mu-lam)}(c*,Delta) - PP_mu H_{N-(mu-lam)}(c*,.) ] at Delta=mu,

  H_N(c*,Delta) = sum_{lam in Kac_N(b*)} sum_k A_{lam,k,N} (Delta-lam)^(-k)   (N >= 1),

where the chain functions
  c^{(k)}_{lam->mu,j}(b) = sum over collision chains g_0,...,g_L from lam to mu of
     R_{g_0} x_{g_0}^(k-1) prod_{i=1..L} R_{g_i}/(x_{g_{i-1}} - x_{g_i}) * x_{g_L}^j / j!,
  x_g(b) = h_g(b) - h_g(b*),
are rational functions of b that are regular at b* (Lemma 3 of the note); the
script checks the regularity and uses their values at b*.  The recursion uses
only fixed-charge blocks H_M(c*,.) (as partial fractions) and these values.

Ground truth: the confluence formula (paper.tex, Thm 7.3 / Thm 12.6), via the
engine in layer2_recursion.py, at every Kac weight and level; optionally
Shapovalov inversion for the torus block at small N.

Usage:
  python3 -u fixed_charge_recursion.py --p 2 --pp 3 --nmax 12 --d 3/7 [--gram-max 6]
  python3 -u fixed_charge_recursion.py --p 2 --pp 3 --nmax 9 --sphere --ext 1/3,2/7,-1/5,3/11
  python3 -u fixed_charge_recursion.py -h | --help
b*^2 = -pp/p (pp may be negative for positive b*^2).
"""

import argparse
import os
import sys
from fractions import Fraction as Fr
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from layer2_recursion import (Model, Ser, ser_add, ser_const, ser_inv,  # noqa: E402
                              ser_mul, ser_sub, ser_poly, log, gram_laurent)


class SphereModel(Model):
    """Same engine with the sphere residues A_{r,s} P_{r,s}(D4,D3) P_{r,s}(D1,D2)."""

    def __init__(self, p, pp, ext, prec):
        super().__init__(p, pp, Fr(0), prec)
        self.ext = [Fr(x) for x in ext]  # Delta_1..Delta_4

    def lam2(self, D):
        # Lambda^2 = Q^2 - 4 Delta = ((nu+1)^2 - 4 Delta nu)/nu  -> (num, den) series
        num = self.nu_poly([1, 2 - 4 * D, 1])
        return ser_mul(num, ser_inv(self.nu_poly([0, 1])))

    def P(self, r, s, Da, Db):
        La2, Lb2 = self.lam2(Da), self.lam2(Db)
        inv_nu = ser_inv(self.nu_poly([0, 1]))
        res = ser_const(1, self.prec)
        js = list(range(1 - r, r, 2))
        ls = list(range(1 - s, s, 2))
        done = set()
        for j in js:
            for l in ls:
                if (j, l) in done:
                    continue
                done.add((j, l))
                done.add((-j, -l))
                if (j, l) == (0, 0):
                    res = ser_mul(res, ser_scale4(ser_sub(La2, Lb2)))
                    continue
                # X = (j b + l/b)^2 = (j nu + l)^2 / nu
                X = ser_mul(self.nu_poly([l * l, 2 * j * l, j * j]), inv_nu)
                d2 = ser_sub(La2, Lb2)
                term = ser_mul(d2, d2)
                term = ser_sub(term, ser_mul(ser_mul(ser_const(2, self.prec), X), ser_add(La2, Lb2)))
                term = ser_add(term, ser_mul(X, X))
                res = ser_mul(res, ser_mul(term, ser_const(Fr(1, 16), self.prec)))
        return res

    def R(self, r, s):
        key = (r, s)
        if key in self._R:
            return self._R[key]
        ser = ser_const(Fr(1, 2), self.prec)
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
        D1, D2, D3, D4 = self.ext
        ser = ser_mul(ser, ser_mul(self.P(r, s, D4, D3), self.P(r, s, D1, D2)))
        self._R[key] = ser
        return ser


def ser_scale4(a):
    return ser_mul(a, ser_const(Fr(1, 4), a.p))


class ChainFunctions:
    """Values at b* of the chain functions c^{(k)}_{lam->mu,j}."""

    def __init__(self, model, nmax, kmax, jmax):
        self.m, self.nmax, self.kmax, self.jmax = model, nmax, kmax, jmax
        self.labels = model.labels(nmax)
        self.weight = {g: model.hstar(*g) for g in self.labels}
        self.x = {g: ser_sub(model.h(*g), ser_const(self.weight[g], model.prec))
                  for g in self.labels}
        self.cache = {}
        self.max_polar = 0

    def table(self, lam):
        """dict (k, mu, j) -> value at b*, for chains from lam of total level <= nmax."""
        if lam in self.cache:
            return self.cache[lam]
        out = {}
        for (k, mu, j), s in self.series(lam).items():
            if s.c and s.v < 0:
                raise ArithmeticError(f"chain function c^({k})_({lam}->{mu},{j}) has a pole of order {-s.v}")
            if s.p < 0:
                raise ArithmeticError("precision exhausted; raise --prec")
            out[(k, mu, j)] = s.coef(0)
        self.cache[lam] = out
        return out

    def series(self, lam):
        """dict (k, mu, j) -> chain function c^{(k)}_{lam->mu,j} as a Laurent series in u."""
        if not hasattr(self, "_series"):
            self._series = {}
        if lam in self._series:
            return self._series[lam]
        m = self.m
        out = {}
        for k in range(1, self.kmax + 1):
            # Q[g] = sum over chains from lam ending with label g of the chain prefactor
            Q = {}
            for g in sorted(self.labels, key=lambda g: (self.weight[g], g)):
                w = self.weight[g]
                if w < lam or w - lam + g[0] * g[1] > self.nmax:
                    continue
                acc = None
                if w == lam:
                    acc = m.R(*g)
                    for _ in range(k - 1):
                        acc = ser_mul(acc, self.x[g])
                else:
                    for gp, qp in Q.items():
                        if self.weight[gp] + gp[0] * gp[1] != w:
                            continue
                        step = ser_mul(m.R(*g), ser_inv(ser_sub(self.x[gp], self.x[g])))
                        term = ser_mul(qp, step)
                        acc = term if acc is None else ser_add(acc, term)
                if acc is not None:
                    Q[g] = acc
            # j-cap check (Theorem 9 valuation bound): val c_j >= min_g val Q[g] + j, so the
            # values at b* vanish for every j > jmax once min_g val Q[g] + jmax + 1 > 0.
            minval = min((q.v for q in Q.values() if q.c), default=1)
            if minval + self.jmax + 1 <= 0:
                raise ArithmeticError(f"--jmax {self.jmax} too small for chains from {lam} (k={k}, valuation {minval})")
            # chain functions: c_{lam->mu,j} = sum_{g: weight+level = mu} Q[g] x_g^j / j!
            sums = {}
            for g, q in Q.items():
                mu = self.weight[g] + g[0] * g[1]
                xp = ser_const(1, m.prec)
                for j in range(self.jmax + 1):
                    term = ser_mul(q, xp)
                    term = Ser(term.v, [c / factorial(j) for c in term.c], term.p)
                    key = (mu, j)
                    sums[key] = term if key not in sums else ser_add(sums[key], term)
                    xp = ser_mul(xp, self.x[g])
            for (mu, j), ser in sums.items():
                out[(k, mu, j)] = ser
        self._series[lam] = out
        return out

    def check_cut(self, lam):
        """Check Lemma 5 exactly as series: j c^(k)_j = c^(k+1)_{j-1} - sum_nu c^(k)_{lam->nu,0} c^(1)_{nu->mu,j-1}."""
        S = self.series(lam)
        weights = sorted(set(self.weight.values()))
        checked = 0
        for (k, mu, j), lhs in S.items():
            if j == 0 or k + 1 > self.kmax:
                continue
            rhs = S.get((k + 1, mu, j - 1))
            if rhs is None:
                continue
            for nu in weights:
                if not (lam < nu < mu) or (nu - lam).denominator != 1:
                    continue
                a = S.get((k, nu, 0))
                if a is None or not (nu in self.weight.values()):
                    continue
                bser = self.series(nu).get((1, mu, j - 1))
                if bser is None:
                    continue
                rhs = ser_sub(rhs, ser_mul(a, bser))
            diff = ser_sub(Ser(lhs.v, [c * j for c in lhs.c], lhs.p), rhs)
            if diff.c:
                raise ArithmeticError(f"cutting identity fails at lam={lam}, mu={mu}, k={k}, j={j}")
            checked += 1
        return checked


def jet(H, M, mu, j):
    """d^j/dDelta^j [H_M(c*,.) - PP_mu H_M] at mu, from stored partial fractions."""
    if M == 0:
        return Fr(1) if j == 0 else Fr(0)
    tot = Fr(0)
    for lam, mom in H[M].items():
        if lam == mu:
            continue
        for k, A in mom.items():
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
    ap.add_argument("--nmax", type=int, required=True)
    ap.add_argument("--d", default="3/7", help="torus external weight")
    ap.add_argument("--sphere", action="store_true")
    ap.add_argument("--ext", default="1/3,2/7,-1/5,3/11", help="sphere Delta_1..Delta_4")
    ap.add_argument("--kmax", type=int, default=6)
    ap.add_argument("--jmax", type=int, default=8)
    ap.add_argument("--prec", type=int, default=30)
    ap.add_argument("--gram-max", type=int, default=0)
    ap.add_argument("--check-cut", action="store_true",
                    help="also verify the cutting identity (Lemma 5) exactly as series at every weight")
    ap.add_argument("--no-truth", action="store_true",
                    help="run the recursion only (no confluence comparison)")
    args = ap.parse_args()

    if args.sphere:
        model = SphereModel(args.p, args.pp, args.ext.split(","), args.prec)
        truth_model = SphereModel(args.p, args.pp, args.ext.split(","), args.prec)
        log(f"sphere block, b*^2 = {model.nu0}, c* = {model.c0}, external weights {args.ext}")
    else:
        model = Model(args.p, args.pp, Fr(args.d), args.prec)
        truth_model = Model(args.p, args.pp, Fr(args.d), args.prec)
        log(f"torus block, b*^2 = {model.nu0}, c* = {model.c0}, d = {args.d}")
    chains = ChainFunctions(model, args.nmax, args.kmax, args.jmax)

    H = {0: {}}  # H[N] = {lam: {k: A}} fixed-charge partial fractions; H_0 = 1
    ok_all = True
    for N in range(1, args.nmax + 1):
        weights = sorted({model.hstar(*g) for g in model.labels(N)})
        HN = {}
        for lam in weights:
            tab = chains.table(lam)
            mom = {}
            for k in range(1, args.kmax + 1):
                A = Fr(0)
                for (kk, mu, j), cval in tab.items():
                    if kk != k or cval == 0 or mu - lam > N:
                        continue
                    A += cval * jet(H, N - int(mu - lam) if (mu - lam).denominator == 1 else None, mu, j)
                if A != 0:
                    mom[k] = A
            if mom.get(args.kmax):
                raise ArithmeticError("raise --kmax")
            HN[lam] = mom
        H[N] = HN
        line = f"N={N:2d}: recursion done ({len(weights)} weights, max pole order " \
               f"{max([max(v) for v in HN.values() if v] or [0])})"
        if not args.no_truth:
            truth = truth_model.principal_parts(N)
            same = all(truth.get(lam, {}) == HN.get(lam, {}) for lam in set(truth) | set(HN))
            line += f"; equals the confluence formula at every Kac weight: {same}"
            ok_all &= same
        log(line)
    if args.gram_max and not args.sphere:
        for lam in sorted({model.hstar(*g) for g in model.labels(args.gram_max)}):
            g = gram_laurent(args.p, args.pp, Fr(args.d), lam, args.gram_max)
            for N in range(1, args.gram_max + 1):
                rec = H[N].get(lam, {})
                ok = all(g[N].get(-k, Fr(0)) == rec.get(k, Fr(0)) for k in range(1, 8))
                ok_all &= ok
                if not ok:
                    log(f"GRAM MISMATCH at lambda={lam}, N={N}")
            log(f"Shapovalov inversion agrees at lambda={lam} for N <= {args.gram_max}")
    if args.check_cut:
        n = 0
        for lam in sorted({model.hstar(*g) for g in model.labels(args.nmax)}):
            n += chains.check_cut(lam)
        log(f"cutting identity (Lemma 5) verified exactly in {n} instances")
    log("ALL OK" if ok_all else "MISMATCH")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
