#!/usr/bin/env python3
"""Exact audit of Lemma 6.8 (one-screening formula at d = h_{1,3}(b)),
Proposition 6.9 (integrality, P_M(0,0) = 4^M, and ell-adic valuation),
and Proposition 6.10 (order, ell-adic valuation, and degree criteria on two-vector levels).

Usage: python3 -u tools/audit_one_screening.py [-h|--help]
"""
import argparse
import math
import os
import sys
from collections import Counter
from fractions import Fraction as Fr
from functools import lru_cache

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import direct_reconstruction as dr  # noqa: E402


def clear_dr_caches():
    for name in dir(dr):
        obj = getattr(dr, name)
        if hasattr(obj, "cache_clear"):
            obj.cache_clear()


def v_l(n, ell):
    if isinstance(n, Fr):
        return v_l(n.numerator, ell) - v_l(n.denominator, ell)
    assert n != 0
    n = abs(n)
    c = 0
    while n % ell == 0:
        n //= ell
        c += 1
    return c


def check_symbolic_lemma_and_PM(Mmax=5):
    """Verify Lemma 6.8 symbolically in Q(t, Delta) and P_M in Z[1/2][t,Y], P_M(0,0)=4^M."""
    t, Delta, Y = sp.symbols("t Delta Y")

    def h_u1(u):
        return ((1 - u * u) * t + 2 * (1 - u)) / 4

    @lru_cache(maxsize=None)
    def R_u1(u):
        num = (-1) ** (u - 1) * (u * t + 1)
        for x in range(1 - u, u + 1):
            num *= (x * t + 2)
        return sp.cancel(num / (2 * sp.factorial(u - 1) * sp.factorial(u) * t ** (2 * u)))

    @lru_cache(maxsize=None)
    def H_rec_shifted(M, u0):
        """H_M(c(t), h_{u0,1}(t) + u0, h_{1,3}(b)) as a rational function of t."""
        if M == 0:
            return sp.Integer(1)
        D0 = h_u1(u0) + u0
        s = sp.Integer(0)
        for u in range(1, M + 1):
            s += sp.cancel(R_u1(u) / (D0 - h_u1(u)) * H_rec_shifted(M - u, u))
        return sp.cancel(s)

    # Compute c_{M,k}(t) symbolically
    gamma = sp.Rational(2, 1) / t

    def binom_sym(g, r):
        res = sp.Integer(1)
        for i in range(r):
            res *= (g - i) / (i + 1)
        return sp.cancel(res)

    def ser_mul(A, B):
        out = [dict() for _ in range(Mmax + 1)]
        for i, a in enumerate(A):
            if not a:
                continue
            for j in range(Mmax + 1 - i):
                b = B[j]
                for ka, va in a.items():
                    for kb, vb in b.items():
                        out[i + j][ka + kb] = sp.cancel(out[i + j].get(ka + kb, sp.Integer(0)) + va * vb)
        return out

    total = [dict() for _ in range(Mmax + 1)]
    total[0][0] = sp.Integer(1)
    for n in range(1, Mmax + 1):
        fac = [dict() for _ in range(Mmax + 1)]
        for r in range(0, Mmax // n + 1):
            coef = sp.cancel(binom_sym(gamma, r) * (-1) ** r)
            for j in range(0, Mmax // n + 1):
                if n * r + n * j <= Mmax:
                    c_inv = sp.binomial(2 * r + j - 1, j) if r > 0 else (1 if j == 0 else 0)
                    if c_inv:
                        fac[n * r + n * j][r] = sp.cancel(
                            fac[n * r + n * j].get(r, sp.Integer(0)) + coef * c_inv
                        )
        total = ser_mul(total, fac)

    for M in range(1, Mmax + 1):
        # Clear common denominator prod_{j=1}^M (2 Delta - 2 h_{j,1}(t))
        factors = [2 * Delta - 2 * h_u1(j) for j in range(1, M + 1)]
        # LHS numerator from generic recursion: sum_{u=1}^M 2 * R_u1(u) * H_rec_shifted(M-u, u) * prod_{j!=u} factors[j-1]
        lhs_num = sp.Integer(0)
        for u in range(1, M + 1):
            term = sp.cancel(2 * R_u1(u) * H_rec_shifted(M - u, u))
            for j in range(1, M + 1):
                if j != u:
                    term *= factors[j - 1]
            lhs_num += term
        # RHS numerator from Lemma 6.8: sum_{k=1}^M c_{M,k} * (-1)^k * prod(jt+2)/(2^k t^k) * prod_{j=k+1}^M factors[j-1]
        rhs_num = sp.Integer(0)
        for k in range(1, M + 1):
            ck = total[M].get(k, sp.Integer(0))
            if ck == 0:
                continue
            num = (-1) ** k
            for j in range(1, 2 * k + 1):
                num *= (j * t + 2)
            term = sp.cancel(ck * num / ((2 ** k) * (t ** k)))
            for j in range(k + 1, M + 1):
                term *= factors[j - 1]
            rhs_num += term
        diff = sp.expand(sp.cancel(t ** (2 * M) * (lhs_num - rhs_num)))
        assert diff == 0, f"Lemma 6.8 symbolic mismatch at M={M}: {diff}"

        PM = sp.expand(sp.cancel((sp.factorial(M) * t ** (2 * M) * rhs_num).subs(Delta, Y / (t * t))))
        poly = sp.Poly(PM, t, Y)
        for c_coeff in poly.coeffs():
            q_c = sp.Rational(c_coeff)
            den_q = int(q_c.q)
            while den_q % 2 == 0:
                den_q //= 2
            assert den_q == 1, f"Odd denominator in P_{M}: {q_c}"
        c00 = PM.subs({t: 0, Y: 0})
        assert c00 == 4 ** M, f"P_{M}(0,0) = {c00} != {4**M}"
    print(f"[PASS] Lemma 6.8 symbolic in Q(t,Delta) and Prop 6.9 P_M in Z[1/2][t,Y], P_M(0,0)=4^M for M=1..{Mmax}", flush=True)


def compute_c_Mk_exact(t, Mmax):
    gamma = Fr(2) / t

    def binom(g, j):
        r = Fr(1)
        for i in range(j):
            r = r * (g - i) / (i + 1)
        return r

    def ser_mul(A, B):
        out = [dict() for _ in range(Mmax + 1)]
        for i, a in enumerate(A):
            if not a:
                continue
            for j in range(Mmax + 1 - i):
                b = B[j]
                for ka, va in a.items():
                    for kb, vb in b.items():
                        out[i + j][ka + kb] = out[i + j].get(ka + kb, Fr(0)) + va * vb
        return out

    total = [dict() for _ in range(Mmax + 1)]
    total[0][0] = Fr(1)
    for n in range(1, Mmax + 1):
        fac = [dict() for _ in range(Mmax + 1)]
        for r in range(0, Mmax // n + 1):
            coef = binom(gamma, r) * (-1) ** r
            for j in range(0, Mmax // n + 1):
                if n * r + n * j <= Mmax:
                    c_inv = math.comb(2 * r + j - 1, j) if r > 0 else (1 if j == 0 else 0)
                    if c_inv:
                        fac[n * r + n * j][r] = fac[n * r + n * j].get(r, Fr(0)) + coef * c_inv
        total = ser_mul(total, fac)
    return total


def eval_HM_h13(t, Delta, M, c_tab):
    def h_u1(u):
        return ((1 - u * u) * t + 2 * (1 - u)) / 4

    res = Fr(0)
    for k, ck in c_tab[M].items():
        num = Fr((-1) ** k)
        for j in range(1, 2 * k + 1):
            num *= (j * t + 2)
        den = (Fr(2) ** k) * (t ** k)
        for j in range(1, k + 1):
            den *= (2 * Delta - 2 * h_u1(j))
        res += ck * num / den
    return res


def check_direct_shapovalov(Mmax=6):
    """Compare Lemma 6.8 directly against Shapovalov inversion (direct_reconstruction.py)."""
    e = [Fr(0)] * (Mmax + 1)
    e[0] = Fr(1)
    for m in range(1, Mmax + 1):
        ne = e[:]
        for i in range(m, Mmax + 1):
            ne[i] -= e[i - m]
        e = ne

    for t, Delta in [(Fr(5, 7), Fr(11, 13)), (Fr(-3, 5), Fr(17, 19))]:
        c = 13 + 6 * (t + 1 / t)
        d = -1 - 2 / t
        dr.C_CHARGE = c
        dr.set_external_weight(d)
        clear_dr_caches()
        F = [Fr(1)]
        for N in range(1, Mmax + 1):
            G = dr.mat_eval(dr.gram_matrix(N), Delta)
            R = dr.mat_eval(dr.vertex_matrix(N), Delta)
            det, tr = dr.det_and_trace_inv(G, R)
            assert det != 0
            F.append(tr)
        H = [sum(e[j] * F[N - j] for j in range(N + 1)) for N in range(Mmax + 1)]
        c_tab = compute_c_Mk_exact(t, Mmax)
        for M in range(Mmax + 1):
            rhs = eval_HM_h13(t, Delta, M, c_tab)
            assert rhs == H[M], f"Direct Shapovalov mismatch at t={t}, Delta={Delta}, M={M}"
    print(f"[PASS] Lemma 6.8 matches direct Shapovalov H_M for M=0..{Mmax} at two generic points", flush=True)


def check_M42_and_89():
    """Check P_42(-5/2, mu*t^2) = 4^42 mod 5 and all 8 valuation-tie levels of (8,9),(3,5),k=1."""
    # First formerly-open Case (a) level: M = 42 (8 divisors) at (p, p') = (2, 5), (r, s) = (1, 1), k = 2?
    # Just pick a valid regular (p, p') = (2, 5), ell = 5, mu with m = 7 (not a Kac weight <= 42)
    p, pp, ell = 2, 5, 5
    t = Fr(-pp, p)
    # Pick interior weight (1,1), layer k=3: l+_3 = (1+2)(1+5)=18, l-_3=(4-1)(10-1)=27, Wait: M=42 in k=6
    # Better: check (p,p')=(8,9), (r,s)=(3,5), k=1, M=42 for P_42 mod 3 AND all 8 ties N in {23,29,32,38,41,47,50,56}!
    p, pp, r, s, k = 8, 9, 3, 5, 1
    t = Fr(-pp, p)
    n0 = pp * r - p * s
    lam = Fr(n0 * n0 - (pp - p) ** 2, 4 * p * pp)
    lp, lm = r * s, (p - r) * (pp - s)
    mup, mum = lam + lp, lam + lm
    c_tab = compute_c_Mk_exact(t, 42)

    # Check P_42 at mup: mod 3 equals 4^42 = 1 mod 3
    H42 = eval_HM_h13(t, mup, 42, c_tab)
    def h_u1(u):
        return ((1 - u * u) * t + 2 * (1 - u)) / 4
    prod_d = Fr(1)
    for u in range(1, 43):
        prod_d *= (2 * mup - 2 * h_u1(u))
    P42 = Fr(math.factorial(42)) * (t ** 84) * prod_d * H42
    assert v_l(P42, 3) == 0
    assert (P42.numerator * pow(P42.denominator, -1, 3)) % 3 == pow(4, 42, 3)
    print("[PASS] Prop 6.9 check at M=42 (8 divisors): P_42(t_star, Y_star) == 4^42 (mod 3) != 0", flush=True)

    # Check all 8 valuation-tie levels of (8,9),(3,5),k=1
    def P_roots(R, S):
        cnt = Counter()
        for kk in range(1, 2 * R, 2):
            for ll in range(1, 2 * S, 2):
                cnt[abs(pp * kk - p * ll)] += 1
                cnt[abs(pp * kk + p * ll)] += 1
        return cnt

    cp, cm = P_roots(r, s), P_roots(p - r, pp - s)
    g = cp & cm
    tp, tm = cp - g, cm - g
    assert sum(tp.values()) == 6 and sum(tm.values()) == 16
    # Degree bound at N = 23 (M+ = 8): 2 + 16 = 18 > 16 = 2*M+
    assert 2 + sum(tm.values()) > 2 * (23 - lp)

    d0 = Fr((pp - 3 * p) ** 2 - (pp - p) ** 2, 4 * p * pp)
    rho = Fr(-n0, 2 * (pp - p))
    def coeff_h13(cnt, sign):
        p0, pd = Fr(1), Fr(1)
        for x, mult in cnt.items():
            dx = Fr(x * x - (pp - p) ** 2, 4 * p * pp)
            if dx != 0:
                p0 *= (-dx) ** mult
            if dx != d0:
                pd *= (d0 - dx) ** mult
        gamma = p0 / (sign * rho)
        return pd / gamma

    c_p, c_m = coeff_h13(cp, +1), coeff_h13(cm, -1)
    for N in [23, 29, 32, 38, 41, 47, 50, 56]:
        val = c_p * eval_HM_h13(t, mup, N - lp, c_tab) + c_m * eval_HM_h13(t, mum, N - lm, c_tab)
        assert val != 0, f"Vanished at N={N}!"
    print("[PASS] Prop 6.10 check on (8,9),(3,5),k=1: degree bound kills N=23; [(d-h_13)^1]P_N != 0 on all 8 tie levels", flush=True)


def check_order_characterization():
    """Verify Prop 6.10(i) order characterization for pp' <= 40, k <= 4."""
    def count_x0(R, S, p, pp):
        x0 = abs(pp - 3 * p)
        c = 0
        for kk in range(1, 2 * R, 2):
            for target in (x0, -x0):
                for num in (target - pp * kk, pp * kk - target):
                    if num > 0 and num % p == 0:
                        ll = num // p
                        if ll % 2 == 1 and ll <= 2 * S - 1:
                            c += 1
        return c

    checked = 0
    for p in range(2, 21):
        for pp in range(3, 41 // p + 1):
            if math.gcd(p, pp) != 1:
                continue
            for r in range(1, p):
                for s in range(1, pp):
                    if pp * r + p * s >= p * pp:
                        continue
                    for k in range(1, 5):
                        if k % 2 == 1:
                            j = (k - 1) // 2
                            ep = count_x0(r + j * p, s + j * pp, p, pp)
                            em = count_x0((j + 1) * p - r, (j + 1) * pp - s, p, pp)
                        else:
                            j = k // 2
                            common = count_x0(r + (j - 1) * p, s + (j - 1) * pp, p, pp)
                            ep = common + count_x0((2 * j - 1) * p + r, pp - s, p, pp)
                            em = common + count_x0(p - r, (2 * j - 1) * pp + s, p, pp)
                        checked += 1
                        if s in (1, pp - 1):
                            assert ep != em
                        else:
                            assert ep == em == k
    print(f"[PASS] Prop 6.10(i) exact order characterization verified on {checked} (p,p',r,s,k) tuples", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.parse_args()
    check_symbolic_lemma_and_PM(5)
    check_direct_shapovalov(6)
    check_M42_and_89()
    check_order_characterization()
    print("ALL ONE-SCREENING AND TWO-TERM AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
