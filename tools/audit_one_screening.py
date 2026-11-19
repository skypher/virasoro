#!/usr/bin/env python3
"""Exact audit of Proposition 6.8 (integrality via Feigin-Fuchs Fock factorization,
level polynomiality, ell-adic valuation, and Lipschitz ratio bound at d = h_{1,+-3}(b))
and Proposition 6.9 (unconditional nonvanishing on all two-vector levels: Cases 1, 2, 3).

Usage: python3 -u tools/audit_one_screening.py [-h|--help]
"""
import argparse
import math
import os
import sys
from collections import Counter, defaultdict
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


def partitions(n, max_part=None):
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for p in range(min(n, max_part), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def check_fock_factorization(Mmax=4):
    """Verify Prop 6.8(i) Feigin-Fuchs Fock factorization G_M = B_M(q0, 2q0-alpha)^T D_M B_M(q0, alpha)."""
    q0, alpha = sp.symbols("q0 alpha")
    c_sym = 1 - 12 * q0 ** 2
    Delta_sym = sp.Rational(1, 2) * alpha * (alpha - 2 * q0)

    def apply_a(k, state):
        """Apply Heisenberg mode a_k ([a_m, a_n] = m delta_{m+n,0}) to linear comb of partition states."""
        out = defaultdict(lambda: sp.Integer(0))
        for part, coeff in state.items():
            if coeff == 0:
                continue
            if k == 0:
                out[part] += coeff * alpha
            elif k < 0:
                np = tuple(sorted(part + (-k,), reverse=True))
                out[np] += coeff
            else:
                # [a_k, a_{-k}^m] = m * k * a_{-k}^{m-1}
                m = part.count(k)
                if m > 0:
                    lst = list(part)
                    lst.remove(k)
                    out[tuple(lst)] += coeff * m * k
        return {p: sp.expand(v) for p, v in out.items() if v != 0}

    def apply_L_neg(n, state):
        """Apply Feigin-Fuchs L_{-n} (n >= 1): 1/2 sum_k :a_k a_{-n-k}: - q0(1-n) a_{-n}."""
        # Terms: k < 0 and -n-k < 0 => -n < k < 0: 1/2 a_k a_{-n-k}
        # k = 0 or -n-k = 0: a_{-n} a_0
        # k > 0 => -n-k < -n: a_{-n-k} a_k (normal ordered: a_{-n-k} left of a_k)
        out = defaultdict(lambda: sp.Integer(0))
        max_mode = max((max(p) if p else 0) for p in state) if state else 0
        # Linear term: -q0*(1 - n)*a_{-n} + a_{-n} a_0 = (alpha - q0*(1-n)) a_{-n}
        s_lin = apply_a(-n, state)
        for p, v in s_lin.items():
            out[p] += v * (alpha - q0 * (1 - n))
        # -n < k < 0: 1/2 a_k a_{-n-k}
        for k in range(1, n):
            s1 = apply_a(-k, apply_a(-(n - k), state))
            for p, v in s1.items():
                out[p] += sp.Rational(1, 2) * v
        # k > 0 (up to max_mode): a_{-n-k} a_k
        for k in range(1, max_mode + 1):
            s1 = apply_a(k, state)
            if s1:
                s2 = apply_a(-n - k, s1)
                for p, v in s2.items():
                    out[p] += v
        return {p: sp.expand(v) for p, v in out.items() if v != 0}

    # Exact Virasoro Gram matrix via recursive vev
    vev_memo = {}

    def vev(modes):
        modes = tuple(modes)
        if modes in vev_memo:
            return vev_memo[modes]
        if sum(modes) != 0:
            return sp.Integer(0)
        if not modes:
            return sp.Integer(1)
        idx = -1
        for i in range(len(modes) - 1, -1, -1):
            if modes[i] >= 0:
                idx = i
                break
        if idx == -1:
            return sp.Integer(0)
        k = modes[idx]
        if k == 0:
            shift = sum(-m for m in modes[idx + 1:])
            res = sp.expand((Delta_sym + shift) * vev(modes[:idx] + modes[idx + 1:]))
            vev_memo[modes] = res
            return res
        if idx == len(modes) - 1:
            return sp.Integer(0)
        b = modes[idx + 1]
        res = vev(modes[:idx] + (b, k) + modes[idx + 2:])
        res += (k - b) * vev(modes[:idx] + (k + b,) + modes[idx + 2:])
        if k + b == 0:
            res += sp.Rational(k ** 3 - k, 12) * c_sym * vev(modes[:idx] + modes[idx + 2:])
        res = sp.expand(res)
        vev_memo[modes] = res
        return res

    for M in range(1, Mmax + 1):
        parts = list(partitions(M))
        dim = len(parts)
        B = sp.zeros(dim, dim)
        D = sp.zeros(dim, dim)
        G = sp.zeros(dim, dim)
        for j, lam in enumerate(parts):
            st = {(): sp.Integer(1)}
            for part in reversed(lam):
                st = apply_L_neg(part, st)
            for i, mu in enumerate(parts):
                val = sp.expand(st.get(mu, sp.Integer(0)))
                B[i, j] = val
                # Check entry in Z[1/2][q0, alpha]
                if val != 0:
                    for coeff in sp.Poly(val, q0, alpha).coeffs():
                        den = int(sp.Rational(coeff).q)
                        while den % 2 == 0:
                            den //= 2
                        assert den == 1, f"Odd denominator in B_{M}: {coeff}"
            cnt = Counter(lam)
            d_val = ((-1) ** len(lam))
            for n_part, mult in cnt.items():
                d_val *= math.factorial(mult) * (n_part ** mult)
            D[j, j] = sp.Integer(d_val)
            assert math.factorial(M) % abs(d_val) == 0
        for i, lam in enumerate(parts):
            for j, mu in enumerate(parts):
                G[i, j] = vev(tuple(reversed(lam)) + tuple(-x for x in mu))
        B_dual = B.subs(alpha, 2 * q0 - alpha)
        prod = (B_dual.T * D * B).applyfunc(sp.expand)
        diff = (G - prod).applyfunc(sp.expand)
        assert diff == sp.zeros(dim, dim), f"Fock factorization mismatch at M={M}"
    print(f"[PASS] Prop 6.8(i) Feigin-Fuchs Fock factorization G_M = B_M(q0,2q0-a)^T D_M B_M(q0,a) in Z[1/2][q0,a] for M=1..{Mmax}", flush=True)


def R_u1_sym(u, t, nu):
    """Exact generic residue R_{u,1}(b, d_nu) as rational function of t = b^2 for nu in {1, 2}."""
    # d_1 = h_{1,3}(b) = -1 - 2/t; d_2 = h_{1,-3}(b) = 2 - 2/t
    # Lambda^2 = (b +- 3 b^{-1})^2 = t +- 6 + 9/t (nu=1: +6, nu=2: -6)
    sgn = 1 if nu == 1 else -1
    # P_{u,1} = prod_{k=1,3,...,2u-1} ((Lambda^2 - (kb + b^{-1})^2)/4) ((Lambda^2 - (kb - b^{-1})^2)/4)
    # Using Lambda^2 - (kb + eps b^{-1})^2 = (1 - k^2)t + (6*sgn - 2*eps*k) + 8/t
    P = sp.Integer(1)
    for k in range(1, 2 * u, 2):
        for eps in (1, -1):
            num = (1 - k * k) * t ** 2 + (6 * sgn - 2 * eps * k) * t + 8
            P *= num / (4 * t)
    # A_{u,1}(b) = 1/2 * prod_{(p,q) in [1-u,u] x [0,1] \ {(0,0),(u,1)}} (p b + q b^{-1})^{-1}
    # q = 0: p in [1-u, u] \ {0}: prod (p b) = (-1)^{u-1} (u-1)! u! b^{2u-1}
    # q = 1: p in [1-u, u-1]: prod (p b + b^{-1}) = b^{1-2u} prod_{p=1-u}^{u-1} (p t + 1)
    # Wait: product of b-powers: b^{2u-1} * b^{1-2u} = 1!
    den = 2 * ((-1) ** (u - 1)) * sp.factorial(u - 1) * sp.factorial(u)
    for p in range(1 - u, u):
        den *= (p * t + 1)
    return sp.cancel(P / den)


def R_u1_exact(u, t, nu):
    """Exact Fraction version of R_{u,1}(b, d_nu) at rational t = b^2."""
    sgn = 1 if nu == 1 else -1
    P = Fr(1)
    for k in range(1, 2 * u, 2):
        for eps in (1, -1):
            P *= ((1 - k * k) * t * t + (6 * sgn - 2 * eps * k) * t + 8) / (4 * t)
    den = Fr(2 * ((-1) ** (u - 1)) * math.factorial(u - 1) * math.factorial(u))
    for p in range(1 - u, u):
        den *= (p * t + 1)
    return P / den


def compute_HM_exact_both(t, Delta, Mmax, nu):
    """Exact H_M(c(b), Delta, d_nu) for M = 0..Mmax via collapsed (u,1) generic recursion."""
    def h_u1(u):
        return ((1 - u * u) * t + 2 * (1 - u)) / 4

    R_tab = [None] + [R_u1_exact(u, t, nu) for u in range(1, Mmax + 1)]
    # Precompute shifted values H_m(h_{u0,1} + u0) for m + u0 <= Mmax
    shifted = {}
    for m in range(0, Mmax + 1):
        for u0 in range(1, Mmax - m + 1):
            if m == 0:
                shifted[(m, u0)] = Fr(1)
            else:
                D0 = h_u1(u0) + u0
                s = Fr(0)
                for u in range(1, m + 1):
                    s += R_tab[u] / (D0 - h_u1(u)) * shifted[(m - u, u)]
                shifted[(m, u0)] = s

    H = [Fr(1)]
    for M in range(1, Mmax + 1):
        s = Fr(0)
        for u in range(1, M + 1):
            s += R_tab[u] / (Delta - h_u1(u)) * shifted[(M - u, u)]
        H.append(s)
    return H


def check_symbolic_PM_and_direct_shapovalov(Mmax_sym=5, Mmax_direct=6):
    """Verify Prop 6.8(i): P_M^{(nu)} in Z[1/2][t,Y], P_M^{(2)}(0,Y)=P_M^{(1)}(0,Y), P_M^{(nu)}(0,0)=4^M,
    and cross-check the collapsed (u,1) recursion against direct Shapovalov inversion for BOTH d_1 and d_2."""
    t, Delta, Y = sp.symbols("t Delta Y")

    def h_u1(u):
        return ((1 - u * u) * t + 2 * (1 - u)) / 4

    P_polys = {1: {}, 2: {}}
    for nu in (1, 2):
        R_tab = {u: R_u1_sym(u, t, nu) for u in range(1, Mmax_sym + 1)}

        @lru_cache(maxsize=None)
        def H_sh(m, u0):
            if m == 0:
                return sp.Integer(1)
            D0 = h_u1(u0) + u0
            s = sp.Integer(0)
            for u in range(1, m + 1):
                s += sp.cancel(R_tab[u] / (D0 - h_u1(u)) * H_sh(m - u, u))
            return sp.cancel(s)

        for M in range(1, Mmax_sym + 1):
            factors = [2 * Delta - 2 * h_u1(j) for j in range(1, M + 1)]
            num = sp.Integer(0)
            for u in range(1, M + 1):
                term = sp.cancel(2 * R_tab[u] * H_sh(M - u, u))
                for j in range(1, M + 1):
                    if j != u:
                        term *= factors[j - 1]
                num += term
            PM = sp.expand(sp.cancel((sp.factorial(M) * t ** (2 * M) * num).subs(Delta, Y / (t * t))))
            poly = sp.Poly(PM, t, Y)
            for c_coeff in poly.coeffs():
                den = int(sp.Rational(c_coeff).q)
                while den % 2 == 0:
                    den //= 2
                assert den == 1, f"Odd denominator in P_{M}^({nu}): {c_coeff}"
            assert PM.subs({t: 0, Y: 0}) == 4 ** M, f"P_{M}^({nu})(0,0) != 4^{M}"
            P_polys[nu][M] = PM

    for M in range(1, Mmax_sym + 1):
        diff0 = sp.expand(P_polys[2][M].subs(t, 0) - P_polys[1][M].subs(t, 0))
        assert diff0 == 0, f"P_{M}^(2)(0,Y) != P_{M}^(1)(0,Y)"
    print(f"[PASS] Prop 6.8(i) symbolic P_M^(1), P_M^(2) in Z[1/2][t,Y], P_M^(2)(0,Y)=P_M^(1)(0,Y), P_M^(nu)(0,0)=4^M for M=1..{Mmax_sym}", flush=True)

    # Cross-check against direct Shapovalov inversion for BOTH d_1 and d_2
    e = [Fr(0)] * (Mmax_direct + 1)
    e[0] = Fr(1)
    for m in range(1, Mmax_direct + 1):
        ne = e[:]
        for i in range(m, Mmax_direct + 1):
            ne[i] -= e[i - m]
        e = ne

    for t_val, D_val in [(Fr(5, 7), Fr(11, 13)), (Fr(-3, 5), Fr(17, 19))]:
        c_val = 13 + 6 * (t_val + 1 / t_val)
        for nu, zeta in [(1, -1), (2, 2)]:
            d_val = zeta - 2 / t_val
            dr.C_CHARGE = c_val
            dr.set_external_weight(d_val)
            clear_dr_caches()
            F = [Fr(1)]
            for N in range(1, Mmax_direct + 1):
                G = dr.mat_eval(dr.gram_matrix(N), D_val)
                R = dr.mat_eval(dr.vertex_matrix(N), D_val)
                det, tr = dr.det_and_trace_inv(G, R)
                assert det != 0
                F.append(tr)
            H_dir = [sum(e[j] * F[N - j] for j in range(N + 1)) for N in range(Mmax_direct + 1)]
            H_rec = compute_HM_exact_both(t_val, D_val, Mmax_direct, nu)
            assert H_dir == H_rec, f"Direct Shapovalov mismatch at nu={nu}, t={t_val}, Delta={D_val}"
    print(f"[PASS] Collapsed (u,1) recursion matches direct Shapovalov H_M at both d_1 and d_2 for M=0..{Mmax_direct}", flush=True)


def check_sl2_and_level_polynomiality():
    """Verify Prop 6.8(ii): exact sl_2 identities (0 <= r,b <= 5) and c_{i,j}^{(nu)}(M) polynomiality
    of degree <= 2i + 2j for all i + j <= 3 across M = 0..8 for both nu = 1, 2."""
    # 1. Verify the two displayed sl_2 identities (and adjoint) in a non-primary sl_2 module
    # Work in Verma module with L_0 |h_0> = h_0 |h_0>, L_1 |h_0> = 0, basis e_k = L_{-1}^k |h_0> (weight h_0 + k)
    h0, d_sym = sp.symbols("h0 d")
    Nmax = 12

    def act_L1(vec):
        # L_1 e_k = k(2 h0 + k - 1) e_{k-1}
        out = {}
        for k, v in vec.items():
            if k > 0 and v != 0:
                out[k - 1] = sp.expand(out.get(k - 1, 0) + v * k * (2 * h0 + k - 1))
        return out

    def act_Lm1(vec):
        return {k + 1: v for k, v in vec.items() if v != 0}

    # Test L_1^r L_{-1}^b on non-primary vector w = e_2 (weight h_w = h0 + 2) for 0 <= r, b <= 5
    for r in range(6):
        for b in range(6):
            # LHS
            lhs = {2: sp.Integer(1)}
            for _ in range(b):
                lhs = act_Lm1(lhs)
            for _ in range(r):
                lhs = act_L1(lhs)
            # RHS
            rhs = {}
            for k in range(min(r, b) + 1):
                c_k = sp.binomial(r, k) * sp.factorial(b) // sp.factorial(b - k)
                v = {2: sp.Integer(1)}
                for _ in range(r - k):
                    v = act_L1(v)
                # Multiply each basis element e_m (L_0 = h0 + m) by prod_{u=0}^{k-1} (2 L_0 + b + r - k - 1 - u)
                v2 = {}
                for m, coeff in v.items():
                    fac = c_k
                    for u in range(k):
                        fac *= (2 * (h0 + m) + b + r - k - 1 - u)
                    v2[m] = sp.expand(coeff * fac)
                for _ in range(b - k):
                    v2 = act_Lm1(v2)
                for m, coeff in v2.items():
                    rhs[m] = sp.expand(rhs.get(m, 0) + coeff)
            all_keys = set(lhs) | set(rhs)
            for m in all_keys:
                assert sp.expand(lhs.get(m, 0) - rhs.get(m, 0)) == 0, f"sl_2 L_1^{r} L_-1^{b} failed at m={m}"

    # Verify <v| L_1^a V_d(1) |W> identity using [L_1, V_d(1)] = (h_L - h_R + d) V_d(1)
    # Represent formal matrix element <v| V_d(1) |W_k> as symbol M_k where W_k = L_1^k |W> (weight h_W - k)
    hv, hW = sp.symbols("hv hW")
    M_syms = [sp.Symbol(f"M_{k}") for k in range(8)]
    # Recursive exact commutation: <v| L_1^a V_d(1) L_1^j |W>
    @lru_cache(maxsize=None)
    def comm_L1(a, j):
        if a == 0:
            return M_syms[j]
        # <v| L_1^{a-1} (L_1 V_d(1)) L_1^j |W> = <v| L_1^{a-1} (V_d(1) L_1 + (d + (hv + a - 1) - (hW - j)) V_d(1)) L_1^j |W>
        # Wait: <v| L_1^{a-1} has weight hv + a - 1!
        return sp.expand(comm_L1(a - 1, j + 1) + (d_sym + (hv + a - 1) - (hW - j)) * comm_L1(a - 1, j))

    for a in range(6):
        lhs = comm_L1(a, 0)
        rhs = sp.Integer(0)
        for mL in range(a + 1):
            fac = sp.binomial(a, mL)
            for u in range(mL):
                fac *= (d_sym + hv - hW + a - 1 - u)
            rhs += fac * M_syms[a - mL]
        assert sp.expand(lhs - rhs) == 0, f"sl_2 L_1^{a} V_d(1) identity failed"
    print("[PASS] Prop 6.8(ii) exact sl_2 identities verified for 0 <= a', r~, b' <= 5", flush=True)

    # 2. Verify c_{i,j}^{(nu)}(M) is a polynomial in M of degree <= 2i + 2j for all i + j <= 3, M = 0..8
    # Compute truncated power series P_M^{(nu)}(t, Y) / 4^M mod (t, Y)^4 using exact Fr arithmetic in Q[t, Y]/(t, Y)^4
    deg_max = 3
    Mmax = 8

    def poly_trunc(d):
        return {(i, j): v for (i, j), v in d.items() if i + j <= deg_max and v != 0}

    def poly_add(a, b):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, Fr(0)) + v
        return poly_trunc(out)

    def poly_mul(a, b):
        out = defaultdict(lambda: Fr(0))
        for (i1, j1), v1 in a.items():
            for (i2, j2), v2 in b.items():
                if i1 + j1 + i2 + j2 <= deg_max:
                    out[(i1 + i2, j1 + j2)] += v1 * v2
        return poly_trunc(out)

    # Compute t^{2u} R_{u,1}(t, d_nu) and t^{2m} H_sh(m, u0) as truncated t-series of length L = TMAX + 2*Mmax.
    # Since t^{2M} prod_{j!=u}(2 Delta - 2 h_{j,1}) = t^2 prod_{j!=u}(2Y + (j-1)t^2 + (j^2-1)/2 t^3),
    # each u-summand of t^{2M-2} P_M^{(nu)}(t,Y) is a polynomial in t, Y; the t^0..t^{2M-3} terms cancel
    # identically across u = 1..M, and extracting [t^{2M-2+i} Y^j] gives [t^i Y^j] P_M^{(nu)}(t, Y).
    TMAX = 4  # need t^0 .. t^3
    L = TMAX + 2 * Mmax

    def tser_mul(a, b, n):
        out = [Fr(0)] * n
        for i in range(n):
            if a[i]:
                for j in range(n - i):
                    out[i + j] += a[i] * b[j]
        return out

    def tser_inv(a, n):
        assert a[0] != 0
        out = [Fr(0)] * n
        inv0 = Fr(1) / a[0]
        out[0] = inv0
        for k in range(1, n):
            s = Fr(0)
            for j in range(1, k + 1):
                s += a[j] * out[k - j]
            out[k] = -s * inv0
        return out

    def poly_interp_check(vals, max_deg):
        """Check vals[0..8] matches a polynomial of degree <= max_deg (finite differences order max_deg+1 == 0)."""
        diffs = list(vals)
        for _ in range(max_deg + 1):
            diffs = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
        assert all(d == 0 for d in diffs), f"Not polynomial of degree <= {max_deg}: diffs={diffs}, vals={vals}"

    for nu in (1, 2):
        sgn = 1 if nu == 1 else -1
        tR = {}
        for u in range(1, Mmax + 1):
            num = [Fr(1)] + [Fr(0)] * (L - 1)
            for k in range(1, 2 * u, 2):
                for eps in (1, -1):
                    fac = [Fr(2), Fr(6 * sgn - 2 * eps * k, 4), Fr(1 - k * k, 4)] + [Fr(0)] * (L - 3)
                    num = tser_mul(num, fac[:L], L)
            den = [Fr(2 * ((-1) ** (u - 1)) * math.factorial(u - 1) * math.factorial(u))] + [Fr(0)] * (L - 1)
            for p in range(1 - u, u):
                fac = [Fr(1), Fr(p)] + [Fr(0)] * (L - 2)
                den = tser_mul(den, fac[:L], L)
            tR[u] = tser_mul(num, tser_inv(den, L), L)

        tH = {}
        for m in range(0, Mmax + 1):
            for u0 in range(1, Mmax - m + 1):
                if m == 0:
                    tH[(m, u0)] = [Fr(1)] + [Fr(0)] * (L - 1)
                else:
                    acc = [Fr(0)] * L
                    for u in range(1, m + 1):
                        d_ser = [Fr(u + u0, 2), Fr(u * u - u0 * u0, 4)] + [Fr(0)] * (L - 2)
                        term = tser_mul(tser_mul(tR[u], tser_inv(d_ser, L), L), tH[(m - u, u)], L)
                        acc = [acc[k] + term[k] for k in range(L)]
                    tH[(m, u0)] = acc

        coeffs_by_ij = defaultdict(list)
        for M in range(0, Mmax + 1):
            if M == 0:
                PM_norm = {(0, 0): Fr(1)}
            else:
                shift = 2 * M - 2
                tmax_M = shift + deg_max  # need t^0 .. t^{shift + deg_max}, Y^0 .. Y^{deg_max}
                # Work with dicts {(i, j): Fr} truncated to i <= tmax_M, j <= deg_max
                PM_shifted = defaultdict(lambda: Fr(0))
                for u in range(1, M + 1):
                    ts = tser_mul(tR[u], tH[(M - u, u)], tmax_M + 1)
                    term = {(i, 0): Fr(2 * math.factorial(M)) * ts[i] for i in range(tmax_M + 1) if ts[i]}
                    for j_idx in range(1, M + 1):
                        if j_idx == u:
                            continue
                        nxt = defaultdict(lambda: Fr(0))
                        c2 = Fr(j_idx - 1)
                        c3 = Fr(j_idx * j_idx - 1, 2)
                        for (ti, yj), val in term.items():
                            if yj + 1 <= deg_max:
                                nxt[(ti, yj + 1)] += val * 2
                            if c2 and ti + 2 <= tmax_M:
                                nxt[(ti + 2, yj)] += val * c2
                            if c3 and ti + 3 <= tmax_M:
                                nxt[(ti + 3, yj)] += val * c3
                        term = {k: v for k, v in nxt.items() if v != 0}
                    for k, v in term.items():
                        PM_shifted[k] += v
                # Verify all negative t-powers (i < shift) vanish identically!
                for (ti, yj), val in PM_shifted.items():
                    if ti < shift:
                        assert val == 0, f"Unregular t-power {ti - shift} at M={M}, nu={nu}, j={yj}: {val}"
                scale = Fr(1, 4 ** M)
                PM_norm = {
                    (ti - shift, yj): val * scale
                    for (ti, yj), val in PM_shifted.items()
                    if ti >= shift and (ti - shift) + yj <= deg_max and val != 0
                }
                assert PM_norm.get((0, 0), Fr(0)) == Fr(1), f"P_{M}^({nu})(0,0)/4^M = {PM_norm.get((0,0), 0)}"
            for i in range(deg_max + 1):
                for j in range(deg_max + 1 - i):
                    coeffs_by_ij[(i, j)].append(PM_norm.get((i, j), Fr(0)))

        for (i, j), vals in coeffs_by_ij.items():
            for v in vals:
                den = v.denominator
                while den % 2 == 0:
                    den //= 2
                assert den == 1, f"Odd denominator in c_{i},{j}^({nu}): {v}"
            poly_interp_check(vals, 2 * i + 2 * j)
    print(f"[PASS] Prop 6.8(ii) exact M-polynomiality of c_{{i,j}}^(nu)(M) (deg <= 2i+2j) for all i+j<=3, M=0..{Mmax}, nu=1,2", flush=True)


def check_valuation_and_lipschitz():
    """Verify Prop 6.8(iii) valuation (eq:h13-valuation) and Lipschitz bound (eq:second-screening-lip),
    including M=42 and all 8 former valuation-tie levels of (8,9),(3,5),k=1."""
    # 1. (8,9),(3,5),k=1: M = 42 at BOTH d_1 and d_2, plus all 8 tie levels
    p, pp, r, s, k = 8, 9, 3, 5, 1
    ell, a = 3, 2
    t = Fr(-pp, p)
    n0 = pp * r - p * s
    lam = Fr(n0 * n0 - (pp - p) ** 2, 4 * p * pp)
    lp, lm = r * s, (p - r) * (pp - s)
    mup, mum = lam + lp, lam + lm
    mp_k = pp * r + p * s
    mm_k = 2 * pp * p - mp_k

    def h_u1(u, tv):
        return ((1 - u * u) * tv + 2 * (1 - u)) / 4

    Hp = {nu: compute_HM_exact_both(t, mup, 42, nu) for nu in (1, 2)}
    Hm = {nu: compute_HM_exact_both(t, mum, 42, nu) for nu in (1, 2)}

    for nu in (1, 2):
        prod_d = Fr(1)
        for u in range(1, 43):
            prod_d *= (2 * mup - 2 * h_u1(u, t))
        P42 = Fr(math.factorial(42)) * (t ** 84) * prod_d * Hp[nu][42]
        assert v_l(P42, 3) == 0
        assert (P42.numerator * pow(P42.denominator, -1, 3)) % 3 == pow(4, 42, 3)
        # Check exact eq:h13-valuation
        expected_v = -v_l(math.factorial(42), 3) - 42 * a - sum(v_l(mp_k ** 2 - (pp * u - p) ** 2, 3) for u in range(1, 43))
        assert v_l(Hp[nu][42], 3) == expected_v

    # Check Lipschitz ratio bound on all 8 tie levels of (8,9),(3,5),k=1
    T1 = -Fr(mm_k * (mm_k ** 2 - p ** 2), mp_k * (mp_k ** 2 - p ** 2))
    assert v_l(T1 - 1, 3) == 1  # v_3(k) + a - v_3(mp_k^2 - p^2) = 0 + 2 - 1 = 1
    for N in [23, 29, 32, 38, 41, 47, 50, 56]:
        Mp, Mm = N - lp, N - lm
        H_rat = (Hp[1][Mp] / Hp[2][Mp]) / (Hm[1][Mm] / Hm[2][Mm])
        assert v_l(H_rat, 3) == 0
        assert v_l(H_rat - 1, 3) >= a  # e = v_3(1) = 0, so >= a = 2
        assert T1 * H_rat != 1

    # 2. Check higher ell-adic Lipschitz bound with e = 1, 2, 3 (ell = 3 and ell = 5)
    # Use (p, pp) = (2, 3), a = 1, M_1 = 3, M_2 in {6, 12, 30} (v_3 = 1, 2, 3)
    for (p0, pp0, ell0, a0, M1, dMs) in [
        (2, 3, 3, 1, 3, [3, 9, 27]),
        (2, 5, 5, 1, 2, [5, 25]),
        (4, 9, 3, 2, 2, [3, 9]),
    ]:
        t0 = Fr(-pp0, p0)
        # Pick Y1, Y2 in ell0^{a0+1} Z_{ell0} with v_{ell0}(Y1 - Y2) >= e + a0
        maxM = M1 + max(dMs)
        Y1 = Fr(ell0 ** (a0 + 1), 7)
        D1 = Y1 / (t0 * t0)
        H1_1 = compute_HM_exact_both(t0, D1, maxM, 1)
        H1_2 = compute_HM_exact_both(t0, D1, maxM, 2)
        for dM in dMs:
            M2 = M1 + dM
            e0 = v_l(dM, ell0)
            Y2 = Y1 + Fr(ell0 ** (e0 + a0), 11)
            D2 = Y2 / (t0 * t0)
            H2_1 = compute_HM_exact_both(t0, D2, M2, 1)
            H2_2 = compute_HM_exact_both(t0, D2, M2, 2)
            # Ratio of P_{M1}^{(1)}/P_{M1}^{(2)} over P_{M2}^{(1)}/P_{M2}^{(2)} equals H-ratio!
            ratio = (H1_1[M1] / H1_2[M1]) / (H2_1[M2] / H2_2[M2])
            assert v_l(ratio, ell0) == 0
            assert ratio == 1 or v_l(ratio - 1, ell0) >= e0 + a0, (
                f"Lipschitz failed at ell={ell0}, a={a0}, e={e0}: v={v_l(ratio-1, ell0)}"
            )
    print("[PASS] Prop 6.8(iii) exact valuation (M=42) and Lipschitz ratio bound (incl. (8,9),(3,5) ties & e=1..3)", flush=True)


def odd_prime_factors(n):
    while n % 2 == 0:
        n //= 2
    res = []
    d = 3
    while d * d <= n:
        if n % d == 0:
            res.append(d)
            while n % d == 0:
                n //= d
        d += 2
    if n >= 3:
        res.append(n)
    return res


def check_case1_case2_case3():
    """Verify Prop 6.9 Cases 1, 2 (both ell >= 5 and ell = 3), and Case 3 (exact epsilon-telescoping
    formula for T_k and ell-adic separation) across all minimal models pp' <= 80, k <= 4."""
    # Case 1: exact order characterization at d_1 and d_2 for pp' <= 40, k <= 4
    def count_target(R, S, p, pp, x_target):
        c = 0
        for a_idx in range(1, 2 * R, 2):
            for l_idx in range(1, 2 * S, 2):
                if abs(pp * a_idx - p * l_idx) == x_target:
                    c += 1
                if pp * a_idx + p * l_idx == x_target:
                    c += 1
        return c

    c1_checked = 0
    for pp in range(3, 41):
        if not odd_prime_factors(pp):
            continue
        for p in range(2, 40 // pp + 1):
            if math.gcd(p, pp) != 1:
                continue
            x1 = abs(pp - 3 * p)
            x2 = pp + 3 * p
            for r in range(1, p):
                for s in range(1, pp):
                    if pp * r + p * s >= p * pp:
                        continue
                    for k in range(1, 5):
                        if k % 2 == 1:
                            j = (k - 1) // 2
                            e1p = count_target(r + j * p, s + j * pp, p, pp, x1)
                            e1m = count_target((j + 1) * p - r, (j + 1) * pp - s, p, pp, x1)
                            e2p = count_target(r + j * p, s + j * pp, p, pp, x2)
                            e2m = count_target((j + 1) * p - r, (j + 1) * pp - s, p, pp, x2)
                        else:
                            j = k // 2
                            c1 = count_target(r + (j - 1) * p, s + (j - 1) * pp, p, pp, x1)
                            c2 = count_target(r + (j - 1) * p, s + (j - 1) * pp, p, pp, x2)
                            e1p = c1 + count_target((2 * j - 1) * p + r, pp - s, p, pp, x1)
                            e1m = c1 + count_target(p - r, (2 * j - 1) * pp + s, p, pp, x1)
                            e2p = c2 + count_target((2 * j - 1) * p + r, pp - s, p, pp, x2)
                            e2m = c2 + count_target(p - r, (2 * j - 1) * pp + s, p, pp, x2)
                        c1_checked += 1
                        if s in (1, pp - 1):
                            assert e1p != e1m
                        else:
                            assert e1p == e1m == k and e2p == e2m == k
    print(f"[PASS] Prop 6.9 Case 1 & 3 order characterization at d_1 and d_2 verified on {c1_checked} tuples", flush=True)

    # Case 2 (both ell >= 5 and ell = 3) and Case 3 (exact T_k and ell-adic separation) on pp' <= 80, k <= 4
    def dtau_block(R, S, p, pp, ell):
        x0, x1 = abs(pp - p), abs(pp - 3 * p)
        tot = 0
        for a_idx in range(1, 2 * R, 2):
            for l_idx in range(1, 2 * S, 2):
                for x in (abs(pp * a_idx - p * l_idx), pp * a_idx + p * l_idx):
                    if x != x1:
                        tot += v_l(x1 * x1 - x * x, ell)
                    if x != x0:
                        tot -= v_l(x0 * x0 - x * x, ell)
        return tot

    def block_ratio_d1_d2(R, S, p, pp):
        """Exact ratio ([(d-d1)^e] P_{R,S}) / ([(d-d2)^e] P_{R,S}) (up to the universal (-(p'-3p)/(p'+3p))^e)."""
        # Actually compute exact ratio of nonzero factors (x1^2 - x^2) / (x2^2 - x^2) for non-common block:
        # Wait: need the branch ratio of [(d-d1)^k] tau^+ / [(d-d1)^k] tau^- over d_2, where the common factor
        # cancels identically and the non-common factors have equal d1 and d2 vanishing orders e_non!
        x1 = abs(pp - 3 * p)
        x2 = pp + 3 * p
        num, den = 1, 1
        e1, e2 = 0, 0
        for a_idx in range(1, 2 * R, 2):
            for l_idx in range(1, 2 * S, 2):
                for x in (abs(pp * a_idx - p * l_idx), pp * a_idx + p * l_idx):
                    if x == x1:
                        e1 += 1
                    else:
                        num *= (x1 * x1 - x * x)
                    if x == x2:
                        e2 += 1
                    else:
                        den *= (x2 * x2 - x * x)
        return Fr(num, den), e1, e2

    c2_ge5 = 0
    c2_eq3 = 0
    c3_checked = 0
    for pp in range(3, 41):
        ells = odd_prime_factors(pp)
        if not ells:
            continue
        for p in range(2, 80 // pp + 1):
            if math.gcd(p, pp) != 1:
                continue
            for r in range(1, p):
                for s in range(2, pp - 1):
                    if pp * r + p * s >= p * pp:
                        continue
                    n0 = pp * r - p * s
                    n1 = pp * r + p * s
                    for k in range(1, 5):
                        if k % 2 == 1:
                            j = (k - 1) // 2
                            Rp, Sp = r + j * p, s + j * pp
                            Rm, Sm = (j + 1) * p - r, (j + 1) * pp - s
                            mp_k = 2 * j * p * pp + n1
                            mm_k = 2 * (j + 1) * p * pp - n1
                        else:
                            j = k // 2
                            Rp, Sp = (2 * j - 1) * p + r, pp - s
                            Rm, Sm = p - r, (2 * j - 1) * pp + s
                            mp_k = 2 * j * p * pp + n0
                            mm_k = 2 * j * p * pp - n0
                        assert Rp * pp + Sp * p == mp_k and Rm * pp + Sm * p == mm_k
                        assert Rp * pp - Sp * p == -(Rm * pp - Sm * p)
                        assert mp_k + mm_k == 2 * k * p * pp

                        # Check Case 2 for every odd prime ell | pp with s != +-1 mod ell
                        for ell in ells:
                            if s % ell not in (1, ell - 1):
                                dp = dtau_block(Rp, Sp, p, pp, ell)
                                dm = dtau_block(Rm, Sm, p, pp, ell)
                                if ell >= 5:
                                    assert dp == 0 and dm == 0, f"Case 2 (ell>=5) fail at {(p,pp,r,s,k,ell)}: {dp},{dm}"
                                    c2_ge5 += 1
                                else:
                                    # ell = 3: each block satisfies dtau == -ord_{d1}(P_{R,S}) * v_3(p' - 3p),
                                    # and since e_+ = e_- = k (common factor equal), dtau_+ = dtau_- = -k v_3(p'-3p)
                                    e1p_b = count_target(Rp, Sp, p, pp, abs(pp - 3 * p))
                                    e1m_b = count_target(Rm, Sm, p, pp, abs(pp - 3 * p))
                                    v3_x1 = v_l(pp - 3 * p, 3)
                                    assert dp == -e1p_b * v3_x1 and dm == -e1m_b * v3_x1, (
                                        f"Case 2 (ell=3) fail at {(p,pp,r,s,k)}: dp={dp}, dm={dm}"
                                    )
                                    assert e1p_b == e1m_b and dp == dm
                                    c2_eq3 += 1

                        # Check Case 3 whenever ANY odd prime ell | pp has s == +-1 mod ell
                        c3_ells = [ell for ell in ells if s % ell in (1, ell - 1)]
                        if c3_ells:
                            rp_val, e1p, e2p = block_ratio_d1_d2(Rp, Sp, p, pp)
                            rm_val, e1m, e2m = block_ratio_d1_d2(Rm, Sm, p, pp)
                            assert e1p == e2p and e1m == e2m
                            Tk_direct = rp_val / rm_val
                            Tk_formula = -Fr(mm_k * (mm_k ** 2 - p ** 2), mp_k * (mp_k ** 2 - p ** 2))
                            assert Tk_direct == Tk_formula, f"Case 3 T_k mismatch at {(p,pp,r,s,k)}"
                            Tk_m1 = -Fr(
                                2 * k * p * pp * (3 * mp_k ** 2 - p ** 2 - 6 * k * p * pp * mp_k + 4 * k * k * p * p * pp * pp),
                                mp_k * (mp_k ** 2 - p ** 2),
                            )
                            assert Tk_formula - 1 == Tk_m1
                            for ell in c3_ells:
                                a_val = v_l(pp, ell)
                                assert v_l(Tk_formula, ell) != 0 or v_l(Tk_formula - 1, ell) <= v_l(k, ell) + a_val - 1
                                c3_checked += 1

    print(
        f"[PASS] Prop 6.9 Case 2 cancellation verified on {c2_ge5} (ell>=5) + {c2_eq3} (ell=3) tuples; "
        f"Case 3 exact T_k & ell-adic separation verified on {c3_checked} tuples",
        flush=True,
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.parse_args()
    check_fock_factorization(4)
    check_symbolic_PM_and_direct_shapovalov(5, 6)
    check_sl2_and_level_polynomiality()
    check_valuation_and_lipschitz()
    check_case1_case2_case3()
    print("ALL TWO-SCREENING, FOCK, POLYNOMIALITY, AND TWO-TERM AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
