#!/usr/bin/env python3
"""Exact rational audit of S1_CONF: fixed-b_* shifted Laurent confluence vs direct Gram matrices.

Implements Definition 5 and Lemma 6 of sphere/notes/s1_confluence.md over exact Q(b_*)((t))
(using exact rational numbers for minimal models b_*^2 = -p'/p by working in u = b^2 - b_*^2;
the grouped numerators C_{lambda,k} are holomorphic at t = 0 so CT_u C_{lambda,k} = CT_t C_{lambda,k})
and verifies exact equality of every collision moment A~^*_{lambda, k, N} against direct
Shapovalov reconstruction of H_N.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Fr
from math import gcd
import sympy as sp

from sphere.tools.exact_sphere_block import reconstruct_B_and_H, peval


# ---------- Exact truncated Laurent series over Fraction in u = b^2 - b_*^2 ----------
# Wait: since h_{r,s}(b) = ((b + 1/b)^2 - (r b + s/b)^2)/4 is a rational function of nu = b^2,
# AND A_{r,s}(b) is a rational function of nu = b^2 (up to b^{2rs-2}? Check!),
# AND P_{r,s}(b, da, db) is a rational function of nu = b^2!
# Let's check: in A_{r,s}(b) = 1/2 prod (p b + q/b)^{-1} over [1-r, r] x [1-s, s] \ {(0,0), (r,s)}:
#   There are (2r)(2s) - 2 = 4rs - 2 factors, and (p b + q/b) = (p nu + q) / b.
#   So A_{r,s}(b) = (1/2) b^{4rs - 2} prod (p nu + q)^{-1} = (1/2) nu^{2rs - 1} prod (p nu + q)^{-1}  (PURELY IN nu = b^2!!).
# In P_{r,s}(b, da, db): pairing (j, l) with (-j, -l) gives factors of the form
#   (L_a^2 + L_b^2 - (j b + l/b)^2)^2 - 4 L_a^2 L_b^2? Wait:
#   ((La+Lb + x)(La-Lb + x))((La+Lb - x)(La-Lb - x)) = ((La+Lb)^2 - x^2)((La-Lb)^2 - x^2)
#   and for (j,l)=(0,0) (when r,s both odd): (La+Lb)/2 * (La-Lb)/2 = (La^2 - Lb^2)/4 = db - da!
#   Notice x^2 = (j b + l/b)^2 = j^2 nu + 2 j l + l^2 / nu (PURELY IN nu = b^2!!),
#   and La^2 = Q^2 - 4 da = nu + 2 + 1/nu - 4 da (PURELY IN nu = b^2!!)!
#   Wait: ((La+Lb)^2 - x^2)((La-Lb)^2 - x^2) = (La^2 + Lb^2 - x^2)^2 - 4 La^2 Lb^2, PURELY IN nu = b^2!!
# THEREFORE h_{r,s}, A_{r,s}, P_{r,s}, AND R^{sph}_{r,s} ARE ALL RATIONAL FUNCTIONS OF nu = b^2 OVER Q!!
# Working in u = nu - nu_* (where nu_* = -p'/p is RATIONAL!) keeps ALL arithmetic in exact Python Fraction!
# Because each grouped numerator C_{lambda,k} is holomorphic at t=0 (verified below by checking
# cancellation of all negative u-powers), its constant term is its value at 0 and satisfies CT_u == CT_t.


class LSeries:
    """Truncated Laurent series sum_{k=val}^{prec} c[k - val] * u^k over Fraction."""

    __slots__ = ("val", "prec", "c")

    def __init__(self, val: int, prec: int, coeffs: list[Fr]):
        # Strip leading zeros
        i = 0
        while i < len(coeffs) and coeffs[i] == 0:
            i += 1
        if i == len(coeffs):
            self.val = prec + 1
            self.prec = prec
            self.c = []
        else:
            self.val = val + i
            self.prec = prec
            keep = min(len(coeffs) - i, prec - self.val + 1)
            self.c = coeffs[i : i + max(0, keep)]

    @classmethod
    def const(cls, x: Fr, prec: int) -> "LSeries":
        if x == 0:
            return cls(prec + 1, prec, [])
        return cls(0, prec, [x] + [Fr(0)] * max(0, prec))

    @classmethod
    def linear(cls, c0: Fr, c1: Fr, prec: int) -> "LSeries":
        arr = [c0, c1] + [Fr(0)] * max(0, prec - 1)
        return cls(0, prec, arr[: prec + 1])

    def is_zero(self) -> bool:
        return not self.c

    def coeff(self, k: int) -> Fr:
        if k > self.prec:
            raise ValueError(f"Requested u^{k} beyond precision u^{self.prec}")
        if k < self.val or k - self.val >= len(self.c):
            return Fr(0)
        return self.c[k - self.val]

    def trunc(self, new_prec: int) -> "LSeries":
        if self.is_zero() or self.val > new_prec:
            return LSeries(new_prec + 1, new_prec, [])
        return LSeries(self.val, new_prec, self.c[: new_prec - self.val + 1])

    def __add__(self, other: "LSeries") -> "LSeries":
        prec = min(self.prec, other.prec)
        if self.is_zero():
            return other.trunc(prec)
        if other.is_zero():
            return self.trunc(prec)
        v = min(self.val, other.val)
        n = prec - v + 1
        out = [Fr(0)] * max(0, n)
        for i, x in enumerate(self.c):
            k = self.val + i - v
            if 0 <= k < n:
                out[k] += x
        for i, x in enumerate(other.c):
            k = other.val + i - v
            if 0 <= k < n:
                out[k] += x
        return LSeries(v, prec, out)

    def __sub__(self, other: "LSeries") -> "LSeries":
        return self + LSeries(other.val, other.prec, [-x for x in other.c])

    def __mul__(self, other: "LSeries") -> "LSeries":
        if self.is_zero() or other.is_zero():
            prec = min(self.prec + other.val, other.prec + self.val)
            return LSeries(prec + 1, prec, [])
        v = self.val + other.val
        prec = min(self.prec + other.val, other.prec + self.val)
        n = prec - v + 1
        if n <= 0:
            return LSeries(prec + 1, prec, [])
        out = [Fr(0)] * n
        for i, x in enumerate(self.c):
            if not x:
                continue
            lim = min(len(other.c), n - i)
            for j in range(lim):
                y = other.c[j]
                if y:
                    out[i + j] += x * y
        return LSeries(v, prec, out)

    def inv(self) -> "LSeries":
        assert not self.is_zero(), "Inverting zero Laurent series"
        # self = u^v * (a0 + a1 u + ... + a_{m} u^m), m = prec - val
        m = self.prec - self.val
        a = self.c + [Fr(0)] * (m + 1 - len(self.c))
        a0 = a[0]
        inv_a = [Fr(0)] * (m + 1)
        inv_a[0] = Fr(1) / a0
        for k in range(1, m + 1):
            s = Fr(0)
            for j in range(1, k + 1):
                if a[j]:
                    s += a[j] * inv_a[k - j]
            inv_a[k] = -s / a0
        return LSeries(-self.val, m - self.val, inv_a)

    def __truediv__(self, other: "LSeries") -> "LSeries":
        return self * other.inv()


def nu_series(nu_star: Fr, prec: int) -> LSeries:
    return LSeries.linear(nu_star, Fr(1), prec)


def h_series(r: int, s: int, nu_star: Fr, prec: int) -> LSeries:
    """h_{r,s}(nu_* + u) = ((1 - r^2) nu + 2(1 - rs) + (1 - s^2)/nu) / 4."""
    nu = nu_series(nu_star, prec)
    inv_nu = nu.inv().trunc(prec)
    t1 = LSeries.const(Fr(1 - r * r, 4), prec) * nu
    t2 = LSeries.const(Fr(1 - r * s, 2), prec)
    t3 = LSeries.const(Fr(1 - s * s, 4), prec) * inv_nu
    return (t1 + t2 + t3).trunc(prec)


def A_series(r: int, s: int, nu_star: Fr, prec: int) -> LSeries:
    """A_{r,s}(nu_* + u) = (1/2) nu^{2rs - 1} / prod_{(p,q)} (p nu + q)."""
    # First count pole order at nu_* to know extra precision needed
    zero_count = 0
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            if p * nu_star + q == 0:
                zero_count += 1
    work = prec + zero_count + 2
    nu = nu_series(nu_star, work)
    # Compute nu^{2rs - 1}
    num = LSeries.const(Fr(1, 2), work)
    base = nu
    exp = 2 * r * s - 1
    while exp > 0:
        if exp & 1:
            num = (num * base).trunc(work)
        base = (base * base).trunc(work)
        exp >>= 1
    den = LSeries.const(Fr(1), work)
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            fac = LSeries.linear(p * nu_star + q, Fr(p), work)
            den = (den * fac).trunc(work + zero_count)
    return (num / den).trunc(prec)


def P_series(r: int, s: int, da: Fr, db: Fr, nu_star: Fr, prec: int) -> LSeries:
    """P_{r,s}(b, da, db) as a Laurent series in u = b^2 - nu_*."""
    work = prec + 2
    nu = nu_series(nu_star, work)
    inv_nu = nu.inv().trunc(work)
    Q2 = nu + LSeries.const(Fr(2), work) + inv_nu
    La2 = Q2 - LSeries.const(Fr(4) * da, work)
    Lb2 = Q2 - LSeries.const(Fr(4) * db, work)
    sumL2 = La2 + Lb2
    fourLa2Lb2 = (LSeries.const(Fr(4), work) * La2 * Lb2).trunc(work)

    # Collect pairs (j, l) with j in 1-r..r-1 step 2, l in 1-s..s-1 step 2
    pairs = [(j, l) for j in range(1 - r, r, 2) for l in range(1 - s, s, 2)]
    seen = set()
    prod = LSeries.const(Fr(1), work)
    for j, l in pairs:
        if (j, l) in seen:
            continue
        if (j, l) == (0, 0):
            seen.add((0, 0))
            # (La^2 - Lb^2)/4 = db - da
            prod = (prod * LSeries.const(db - da, work)).trunc(work)
        else:
            seen.add((j, l))
            seen.add((-j, -l))
            # x^2 = j^2 nu + 2 j l + l^2 / nu
            x2 = (
                LSeries.const(Fr(j * j), work) * nu
                + LSeries.const(Fr(2 * j * l), work)
                + LSeries.const(Fr(l * l), work) * inv_nu
            ).trunc(work)
            diff = sumL2 - x2
            # ((La+Lb)^2 - x^2)((La-Lb)^2 - x^2) / 16 = ((La^2 + Lb^2 - x^2)^2 - 4 La^2 Lb^2) / 16
            fac = ((diff * diff - fourLa2Lb2) * LSeries.const(Fr(1, 16), work)).trunc(work)
            prod = (prod * fac).trunc(work)
    return prod.trunc(prec)


def R_series(r: int, s: int, d_ext: tuple[Fr, Fr, Fr, Fr], nu_star: Fr, prec: int) -> LSeries:
    d1, d2, d3, d4 = d_ext
    # Find pole order of A_{r,s} to keep precision
    A0 = A_series(r, s, nu_star, 0)
    pi = max(0, -A0.val)
    work = prec + pi + 2
    A = A_series(r, s, nu_star, prec + 2)
    P43 = P_series(r, s, d4, d3, nu_star, work)
    P12 = P_series(r, s, d1, d2, nu_star, work)
    return (A * P43 * P12).trunc(prec)


def compute_collision_moments(nu_star: Fr, d_ext: tuple[Fr, Fr, Fr, Fr], max_level: int):
    """Run the exact shifted Laurent confluence recursion with backward precision budget."""
    labels_by_max = {
        M: [(r, s) for r in range(1, M + 1) for s in range(1, M // r + 1)]
        for M in range(max_level + 1)
    }

    # Exact valuations pi_g, sigma_{a,g}, and a priori bounds W_{a, M}
    pi_val = {}
    for g in labels_by_max[max_level]:
        Rg0 = R_series(g[0], g[1], d_ext, nu_star, 0)
        pi_val[g] = max(0, -Rg0.val)

    sigma_val = {}
    for a in labels_by_max[max_level]:
        za = h_series(a[0], a[1], nu_star, 4) + LSeries.const(Fr(a[0] * a[1]), 4)
        for g in labels_by_max[max_level]:
            diff = za - h_series(g[0], g[1], nu_star, 4)
            assert not diff.is_zero(), f"z_{a} - h_{g} vanished identically!"
            sigma_val[(a, g)] = max(0, diff.val)

    W = {}
    for M in range(max_level + 1):
        for a in labels_by_max[max_level]:
            if M == 0:
                W[(a, 0)] = 0
            else:
                best = 0
                for g in labels_by_max[M]:
                    cand = pi_val[g] + sigma_val[(a, g)] + W[(g, M - g[0] * g[1])]
                    if cand > best:
                        best = cand
                W[(a, M)] = best

    # Backward precision budget (Lemma 6)
    need_S = {}
    def request_S(a, M, U):
        if U > need_S.get((a, M), -10**9):
            need_S[(a, M)] = U
            if M > 0:
                for g in labels_by_max[M]:
                    request_S(g, M - g[0] * g[1], U + pi_val[g] + sigma_val[(a, g)])

    for N in range(1, max_level + 1):
        for a in labels_by_max[N]:
            request_S(a, N - a[0] * a[1], pi_val[a])

    # Compute S_{a, M} bottom-up in M with exact required precision
    S_cache = {}
    R_cache = {}
    def get_R(g, prec):
        if g not in R_cache or R_cache[g].prec < prec:
            R_cache[g] = R_series(g[0], g[1], d_ext, nu_star, prec)
        return R_cache[g].trunc(prec)

    for M in range(max_level + 1):
        for (a, m), U in list(need_S.items()):
            if m != M:
                continue
            if M == 0:
                S_cache[(a, 0)] = LSeries.const(Fr(1), max(0, U))
            else:
                acc = LSeries(U + 1, U, [])
                for g in labels_by_max[M]:
                    rem = M - g[0] * g[1]
                    Wg = W[(g, rem)]
                    sig = sigma_val[(a, g)]
                    pi_g = pi_val[g]
                    # Need R_g / (z_a - h_g) through u^{U + Wg}
                    prec_ratio = U + Wg
                    Rg = get_R(g, prec_ratio + sig)
                    za = h_series(a[0], a[1], nu_star, prec_ratio + pi_g + sig + 2) + LSeries.const(Fr(a[0] * a[1]), prec_ratio + pi_g + sig + 2)
                    hg = h_series(g[0], g[1], nu_star, prec_ratio + pi_g + sig + 2)
                    ratio = (Rg / (za - hg)).trunc(prec_ratio)
                    Sg = S_cache[(g, rem)].trunc(U + pi_g + sig)
                    acc = acc + (ratio * Sg).trunc(U)
                S_cache[(a, M)] = acc.trunc(U)

    # Extract collision moments for every N = 1..max_level
    moments_by_level = {}
    for N in range(1, max_level + 1):
        fibers: dict[Fr, list[tuple[int, int]]] = {}
        for a in labels_by_max[N]:
            lam = h_series(a[0], a[1], nu_star, 0).coeff(0)
            fibers.setdefault(lam, []).append(a)
        level_res = {}
        for lam, fiber in fibers.items():
            # Compute B_{a, N} through u^0 and delta_a through u^{vhat}
            max_k = 1
            B_list = []
            for a in fiber:
                vhat = pi_val[a] + W[(a, N - a[0] * a[1])]
                Ra = get_R(a, W[(a, N - a[0] * a[1])])
                Sa = S_cache[(a, N - a[0] * a[1])].trunc(pi_val[a])
                Ba = (Ra * Sa).trunc(0)
                ha = h_series(a[0], a[1], nu_star, vhat + 2)
                delta = (ha - LSeries.const(lam, vhat + 2)).trunc(vhat + 2)
                eps = None if delta.is_zero() else delta.val
                if eps is not None:
                    max_k = max(max_k, 1 + vhat // eps)
                B_list.append((Ba, delta, vhat))
            # Check cancellation of negative powers of u in sum B_a * delta_a^{k-1}
            moms = {}
            for k in range(1, max_k + 1):
                tot = LSeries(1, 0, [])
                for Ba, delta, vhat in B_list:
                    if k == 1:
                        dpow = LSeries.const(Fr(1), vhat)
                    elif delta.is_zero():
                        dpow = LSeries(vhat + 1, vhat, [])
                    else:
                        dpow = LSeries.const(Fr(1), vhat)
                        for _ in range(k - 1):
                            dpow = (dpow * delta).trunc(vhat)
                    tot = tot + (Ba * dpow).trunc(0)
                # Verify all negative powers of u vanished!
                for neg in range(tot.val, 0):
                    assert tot.coeff(neg) == 0, f"Pole cancellation failed at N={N}, lam={lam}, k={k}, u^{neg}: {tot.coeff(neg)}"
                ct = tot.coeff(0)
                if ct != 0:
                    moms[k] = ct
            level_res[lam] = moms
        moments_by_level[N] = level_res
    return moments_by_level


def audit_irrational_b(max_level: int = 4) -> None:
    print(f"=== Auditing irrational b_*^2 = sqrt(2) (symbolic, N=1..{max_level}) ===", flush=True)
    # At irrational b^2, all Kac weights are distinct and all poles are simple, with no collisions!
    # Check generic Zamolodchikov recursion directly against Gram-matrix H_N at nu = sqrt(2) (exact in Q(sqrt(2)))!
    # For clean exact verification, pick a non-rational algebraic value via sympy or check rational non-minimal nu = 5/7 first,
    # and symbolic sqrt(2) via sympy!
    s2 = sp.sqrt(2)
    c_val = sp.simplify(1 + 6 * (s2 + 2 + 1 / s2))  # c = 13 + 6*(nu + 1/nu) = 13 + 9*sqrt(2)
    h = sp.Symbol("h")
    # External weights d = (1/3, 2/5, 3/7, 5/11)
    d1, d2, d3, d4 = sp.Rational(1, 3), sp.Rational(2, 5), sp.Rational(3, 7), sp.Rational(5, 11)

    def h_rs(r, s):
        return sp.simplify(((1 - r**2) * s2 + 2 * (1 - r * s) + (1 - s**2) / s2) / 4)

    def A_rs(r, s):
        prod = sp.Integer(1)
        for p in range(1 - r, r + 1):
            for q in range(1 - s, s + 1):
                if (p, q) in ((0, 0), (r, s)):
                    continue
                prod *= (p * s2 + q)
        return sp.simplify(sp.Rational(1, 2) * s2**(2 * r * s - 1) / prod)

    def P_rs(r, s, da, db):
        Q2 = s2 + 2 + 1 / s2
        La2, Lb2 = Q2 - 4 * da, Q2 - 4 * db
        pairs = [(j, l) for j in range(1 - r, r, 2) for l in range(1 - s, s, 2)]
        seen = set()
        prod = sp.Integer(1)
        for j, l in pairs:
            if (j, l) in seen:
                continue
            if (j, l) == (0, 0):
                seen.add((0, 0))
                prod *= (db - da)
            else:
                seen.add((j, l))
                seen.add((-j, -l))
                x2 = j**2 * s2 + 2 * j * l + l**2 / s2
                prod *= ((La2 + Lb2 - x2)**2 - 4 * La2 * Lb2) / 16
        return sp.simplify(prod)

    # Build H_N via Zamolodchikov recursion at nu = sqrt(2) and verify at h = 5 against direct Gram matrix!
    H_rec = {0: sp.Integer(1)}
    for N in range(1, max_level + 1):
        expr = sp.Integer(0)
        for r in range(1, N + 1):
            for s in range(1, N // r + 1):
                hrs = h_rs(r, s)
                R = sp.simplify(A_rs(r, s) * P_rs(r, s, d4, d3) * P_rs(r, s, d1, d2))
                H_sub = H_rec[N - r * s].subs(h, hrs + r * s)
                expr += R * H_sub / (h - hrs)
        H_rec[N] = expr

    # Direct Gram matrix at h = 5, c = 13 + 9*sqrt(2)
    from sphere.tools.exact_sphere_block import partitions, normal_order
    # Quick symbolic Gram check up to level 3 (fast)
    h_test = sp.Integer(5)
    # Compare with exact symbolic B_N and H_N at h = 5 for N = 1..min(3, max_level)
    chk_N = min(3, max_level)
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def act(m, word):
        if not word:
            return {}
        n, rest = word[0], word[1:]
        out = {}
        for w, val in act(m, rest).items():
            for w2, cf in normal_order((n,) + w).items():
                out[w2] = out.get(w2, 0) + val * cf
        k = m + n
        if k < 0:
            for w2, cf in normal_order((k,) + rest).items():
                out[w2] = out.get(w2, 0) + (m - n) * cf
        elif k == 0:
            lvl = -sum(rest)
            out[rest] = out.get(rest, 0) + (m - n) * (h_test + lvl) + c_val * (m**3 - m) / 12
        else:
            for w2, val in act(k, rest).items():
                out[w2] = out.get(w2, 0) + (m - n) * val
        return {w: sp.expand(v) for w, v in out.items() if sp.simplify(v) != 0}

    B_vals = [sp.Integer(1)]
    for lvl in range(1, chk_N + 1):
        basis = list(partitions(lvl))
        n = len(basis)
        G = sp.Matrix(n, n, lambda i, j: 0)
        for i in range(n):
            for j in range(i, n):
                comb = {tuple(-x for x in basis[j]): sp.Integer(1)}
                for mode in basis[i]:
                    nxt = {}
                    for w, v in comb.items():
                        for w2, v2 in act(mode, w).items():
                            nxt[w2] = nxt.get(w2, 0) + v * v2
                    comb = nxt
                G[i, j] = sp.simplify(comb.get((), 0))
                G[j, i] = G[i, j]
        def gvec(da, db):
            out = []
            for Y in basis:
                prod = sp.Integer(1)
                for idx in range(len(Y)):
                    prod *= (h_test + sum(Y[idx + 1:]) + Y[idx] * db - da)
                out.append(prod)
            return sp.Matrix(out)
        vL, vR = gvec(d4, d3), gvec(d1, d2)
        B_vals.append(sp.simplify((vL.T * G.inv() * vR)[0]))

    q = sp.Symbol("q")
    th3 = 1 + 2 * q + 2 * q**4
    th4 = 1 - 2 * q + 2 * q**4
    z_q = sp.series(1 - (th4 / th3)**4, q, 0, chk_N + 2).removeO()
    z16 = sp.series(z_q / (16 * q), q, 0, chk_N + 1).removeO()
    omz = sp.series((th4 / th3)**4, q, 0, chk_N + 1).removeO()
    pref = sp.series(
        z16**(h_test - (c_val - 1) / 24)
        * omz**(d2 + d3 - (c_val - 1) / 24)
        * th3**(4 * (d1 + d2 + d3 + d4) - (c_val - 1) / 2),
        q, 0, chk_N + 1,
    ).removeO()
    Bz = sum(B_vals[m] * z_q**m for m in range(chk_N + 1))
    Hq = sp.series(pref * Bz, q, 0, chk_N + 1).removeO()
    for N in range(1, chk_N + 1):
        h_dir = sp.simplify(Hq.coeff(q, N) / 16**N)
        h_rec = sp.simplify(H_rec[N].subs(h, h_test))
        assert sp.simplify(h_dir - h_rec) == 0, f"Irrational b mismatch at N={N}: {sp.simplify(h_dir - h_rec)}"
    print(f"  [PASS] b_*^2 = sqrt(2): exact match with direct Gram matrix for N=1..{chk_N}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit S1_CONF fixed-b_* shifted Laurent confluence.")
    parser.add_argument("--max-level", type=int, default=7, help="Max level for minimal-model audits (default: 7)")
    args = parser.parse_args()
    N_max = args.max_level

    d_ext = (Fr(1, 5), Fr(2, 7), Fr(3, 11), Fr(4, 13))
    models = [(2, 3), (2, 5), (3, 4)]

    for p, pp in models:
        nu_star = Fr(-pp, p)
        c_val = Fr(1) - Fr(6 * (pp - p)**2, p * pp)
        print(f"=== Auditing minimal model ({p}, {pp}), c = {c_val}, N = 1..{N_max} ===", flush=True)
        moms = compute_collision_moments(nu_star, d_ext, N_max)
        _, H_funcs = reconstruct_B_and_H(c_val, d_ext, N_max)

        for N in range(1, N_max + 1):
            # Verify exact pole-by-pole Laurent principal parts at every frozen pole lambda,
            # plus global rational equality at the non-pole test point h = 17/3.
            for lam, mdict in moms[N].items():
                ord_H, laurent = H_funcs[N].laurent_at(lam, 0)
                max_k_conf = max(mdict.keys()) if mdict else 0
                assert ord_H == max_k_conf, f"({p},{pp}) N={N} lam={lam}: ord_H={ord_H} != max_k_conf={max_k_conf}"
                for k in range(1, ord_H + 1):
                    c_dir = laurent.get(-k, Fr(0))
                    c_conf = mdict.get(k, Fr(0))
                    assert c_dir == c_conf, f"({p},{pp}) N={N} lam={lam} k={k}: direct={c_dir} != conf={c_conf}"
            # Also verify sum of partial fractions equals H_N(h) at a non-pole test point h = 17/3
            h_pt = Fr(17, 3)
            lhs = H_funcs[N].eval(h_pt)
            rhs = sum(
                val / (h_pt - lam)**k
                for lam, mdict in moms[N].items()
                for k, val in mdict.items()
            )
            assert lhs == rhs, f"({p},{pp}) N={N}: global rational mismatch at h={h_pt}: {lhs} != {rhs}"
        print(f"  [PASS] ({p},{pp}): exact match of ALL collision moments & global rational H_N for N=1..{N_max}", flush=True)

    audit_irrational_b(3)
    print("\nALL S1_CONF AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
