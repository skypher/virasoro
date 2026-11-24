#!/usr/bin/env python3
"""Exact rational and symbolic audit for irreducible minimal-model torus one-point traces.

Verifies all three main theorems of irreducible/paper.tex in exact arithmetic:
  1. Fusion-descent criterion and exact regularity iff (Theorem 1).
  2. Two-weight Ward symmetry, product-rule derivative identity, rectangle formula,
     and Gamma-potential cocycle factorization for c_{R,S}(t; 2k+1, 2m+1) (Theorem 2).
  3. Generalized Rocha-Caridi / BGG alternating-sum identity and collision-free
     single-index recursion against direct quotient-Gram traces (Theorem 3 & Cor. 1),
     covering Lee-Yang (2,5), Ising (3,4), Tricritical Ising (4,5) (all three nonzero
     fusion insertions including the two-index case h_{3,3}), and (3,5).
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import os
import sys
import sympy as sp

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
sys.path.insert(0, REPO_ROOT)
import tools.direct_reconstruction as dr
import tools.exact_shapovalov as es


# ---------------------------------------------------------------- exact linear algebra

def rref_pivots(M):
    m = len(M)
    if m == 0:
        return []
    n = len(M[0])
    A = [row[:] for row in M]
    pivs = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = Fraction(1) / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(n)]
        pivs.append(c)
        r += 1
    return pivs


def nullspace_Q(M):
    m = len(M)
    n = len(M[0])
    A = [row[:] for row in M]
    pivs = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = Fraction(1) / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(n)]
        pivs.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivs]
    vecs = []
    for f in free:
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for idx, p in enumerate(pivs):
            v[p] = -A[idx][f]
        vecs.append(v)
    return vecs


def mat_inv_Q(M):
    n = len(M)
    A = [M[i][:] + [Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        inv = Fraction(1) / A[c][c]
        A[c] = [v * inv for v in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[c][j] for j in range(2 * n)]
    return [row[n:] for row in A]


def set_cd(c_val, d_val):
    dr.C_CHARGE = Fraction(c_val)
    dr.act.cache_clear()
    dr.set_external_weight(Fraction(d_val))


def direct_quotient_trace(c_val, h_val, d_val, maxN):
    """Return list of (N, dim_L, descends, trace_or_None) in exact Q."""
    set_cd(c_val, d_val)
    out = []
    for N in range(maxN + 1):
        G = dr.mat_eval(dr.gram_matrix(N), Fraction(h_val))
        R = dr.mat_eval(dr.vertex_matrix(N), Fraction(h_val))
        ns = nullspace_Q(G)
        # Check radical descent: R * v == 0 for every v in ker(G)
        desc = True
        for v in ns:
            for row in R:
                if sum(a * b for a, b in zip(row, v)) != 0:
                    desc = False
                    break
            if not desc:
                break
        pivs = rref_pivots(G)
        if not desc:
            out.append((N, len(pivs), False, None))
            continue
        Gs = [[G[i][j] for j in pivs] for i in pivs]
        Rs = [[R[i][j] for j in pivs] for i in pivs]
        Gi = mat_inv_Q(Gs)
        tr = sum(Gi[i][j] * Rs[j][i] for i in range(len(pivs)) for j in range(len(pivs)))
        out.append((N, len(pivs), True, tr))
    return out


# ---------------------------------------------------------------- exact Q((x)) Laurent trace

def shift_poly_Q(poly, a):
    out = [Fraction(0)] * len(poly)
    cur = [Fraction(1)]
    for coeff in poly:
        for i, v in enumerate(cur):
            out[i] += coeff * v
        nxt = [Fraction(0)] * (len(cur) + 1)
        for i, v in enumerate(cur):
            nxt[i] += v * a
            nxt[i + 1] += v
        cur = nxt
    return out


def laurent_trace_Q(Gpoly, Rpoly, h0, order=4):
    """Exact Laurent series of Tr(G(h0 + x)^{-1} R(h0 + x)) in Q((x))."""
    n = len(Gpoly)
    prec = order + 3

    def s_norm(val, c):
        i = 0
        while i < len(c) and c[i] == 0:
            i += 1
        if i == len(c):
            return (10**9, [])
        return (val + i, c[i:i + prec])

    def s_add(a, b):
        if not a[1]:
            return b
        if not b[1]:
            return a
        v = min(a[0], b[0])
        out = [Fraction(0)] * prec
        for k in range(prec):
            deg = v + k
            s = Fraction(0)
            if a[0] <= deg < a[0] + len(a[1]):
                s += a[1][deg - a[0]]
            if b[0] <= deg < b[0] + len(b[1]):
                s += b[1][deg - b[0]]
            out[k] = s
        return s_norm(v, out)

    def s_sub(a, b):
        return s_add(a, (b[0], [-x for x in b[1]]))

    def s_mul(a, b):
        if not a[1] or not b[1]:
            return (10**9, [])
        out = [Fraction(0)] * prec
        for i, x in enumerate(a[1]):
            if x == 0:
                continue
            for j, y in enumerate(b[1]):
                if i + j >= prec:
                    break
                if y != 0:
                    out[i + j] += x * y
        return s_norm(a[0] + b[0], out)

    def s_inv(a):
        a0i = Fraction(1) / a[1][0]
        out = [a0i]
        for k in range(1, prec):
            s = Fraction(0)
            for i in range(1, min(k + 1, len(a[1]))):
                s += a[1][i] * out[k - i]
            out.append(-s * a0i)
        return (-a[0], out)

    A = [[s_norm(0, shift_poly_Q(Gpoly[i][j], h0)[:prec]) for j in range(n)] for i in range(n)]
    B = [[s_norm(0, shift_poly_Q(Rpoly[i][j], h0)[:prec]) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = min(range(col, n), key=lambda r: A[r][col][0])
        assert A[piv][col][1], f"singular at col {col}"
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            B[col], B[piv] = B[piv], B[col]
        inv_p = s_inv(A[col][col])
        for j in range(col, n):
            A[col][j] = s_mul(A[col][j], inv_p)
        for j in range(n):
            B[col][j] = s_mul(B[col][j], inv_p)
        for i in range(n):
            if i != col and A[i][col][1]:
                f = A[i][col]
                A[i][col] = (10**9, [])
                for j in range(col + 1, n):
                    if A[col][j][1]:
                        A[i][j] = s_sub(A[i][j], s_mul(f, A[col][j]))
                for j in range(n):
                    if B[col][j][1]:
                        B[i][j] = s_sub(B[i][j], s_mul(f, B[col][j]))
    tr = (10**9, [])
    for i in range(n):
        tr = s_add(tr, B[i][i])
    return tr


# ---------------------------------------------------------------- box & BGG helpers

def c_box(p, pp, R, S, u, v):
    k, m = (u - 1) // 2, (v - 1) // 2
    top = {(a, b) for a in range(1 - R + k, R + k + 1) for b in range(1 - S + m, S + m + 1)}
    bot = {(a, b) for a in range(1 - R, R + 1) for b in range(1 - S, S + 1)}
    num, den = 1, 1
    for (a, b) in (top - bot):
        val = p * b - pp * a
        assert val != 0
        num *= val
    for (a, b) in (bot - top):
        val = p * b - pp * a
        assert val != 0
        den *= val
    return Fraction(num, den)


def bgg_terms(p, pp, r, s, u, v, maxN):
    n0 = pp * r - p * s

    def find_RS(n_from, n_to):
        for sgn in (+1, -1):
            if (n_to + sgn * n_from) % (2 * pp) == 0 and (n_to - sgn * n_from) % (2 * p) == 0:
                R = (n_to + sgn * n_from) // (2 * pp)
                S = (n_to - sgn * n_from) // (2 * p)
                if R > 0 and S > 0:
                    return (R, S)
        raise ValueError(f"No BGG arrow {n_from} -> {n_to}")

    terms = [(0, 0, n0, Fraction(1))]
    layers = [[(n0, Fraction(1))]]
    for k in range(1, 30):
        j = (k + 1) // 2
        if k % 2 == 1:
            ns = [2 * (j - 1) * p * pp + (pp * r + p * s), 2 * j * p * pp - (pp * r + p * s)]
        else:
            ns = [2 * j * p * pp - n0, 2 * j * p * pp + n0]
        prev_n, prev_a = layers[-1][0]
        cur_layer = []
        for nt in ns:
            lv = (nt * nt - n0 * n0) // (4 * p * pp)
            if lv <= maxN:
                R, S = find_RS(prev_n, nt)
                a = -prev_a * c_box(p, pp, R, S, u, v)
                # Also verify diamond cocycle against second parent if present!
                if len(layers[-1]) == 2:
                    prev_n2, prev_a2 = layers[-1][1]
                    R2, S2 = find_RS(prev_n2, nt)
                    a2 = -prev_a2 * c_box(p, pp, R2, S2, u, v)
                    assert a == a2, f"Cocycle mismatch: {a} vs {a2}"
                cur_layer.append((nt, a))
                terms.append((k, lv, nt, a))
        if not cur_layer:
            break
        layers.append(cur_layer)
    return terms


# ---------------------------------------------------------------- CHECK 1: Theorem 1

def audit_theorem1():
    print("[1/4] Auditing Lemma 2.3(iv) transverse slope & Theorem 1 (fusion-descent & regularity iff)...", flush=True)
    # 1a. Verify exact Lemma 2.3(iv) transverse-slope formula (m2*n2 - m1*n1)/(4*pp^2)
    t_sym = sp.Symbol("t")

    def h_t(R, S):
        return ((t_sym + 1) ** 2 - (R * t_sym + S) ** 2) / (4 * t_sym)

    for (p, pp, r, s) in [(2, 3, 1, 1), (2, 5, 1, 2), (3, 4, 1, 2), (4, 5, 2, 2), (3, 5, 1, 2)]:
        n0 = pp * r - p * s
        n1 = pp * r + p * s
        t0 = sp.Rational(-pp, p)
        # Check layers k = 0, 1, 2
        layer_momenta = [[n0], [n1, 2 * p * pp - n1], [2 * p * pp - n0, 2 * p * pp + n0], [2 * p * pp + n1, 4 * p * pp - n1]]
        for k_lay in range(3):
            for n_mu in layer_momenta[k_lay]:
                children = layer_momenta[k_lay + 1]
                arrows = []
                for n_nu in children:
                    found = []
                    for sgn in (+1, -1):
                        if (n_nu + sgn * n_mu) % (2 * pp) == 0 and (n_nu - sgn * n_mu) % (2 * p) == 0:
                            R = (n_nu + sgn * n_mu) // (2 * pp)
                            S = (n_nu - sgn * n_mu) // (2 * p)
                            if R > 0 and S > 0:
                                found.append((R, S))
                    assert len(found) == 1
                    arrows.append(found[0])
                (R1, S1), (R2, S2) = arrows
                deriv_exact = sp.diff(h_t(R1, S1) - h_t(R2, S2), t_sym).subs(t_sym, t0)
                m1, n_1 = pp * R1 - p * S1, pp * R1 + p * S1
                m2, n_2 = pp * R2 - p * S2, pp * R2 + p * S2
                formula = sp.Rational(m2 * n_2 - m1 * n_1, 4 * pp * pp)
                assert deriv_exact == formula and formula != 0, f"Slope mismatch: {deriv_exact} vs {formula}"
    # Spot check (2,3) vacuum: (1,1),(1,2) -> -1/3
    assert sp.diff(h_t(1, 1) - h_t(1, 2), t_sym).subs(t_sym, sp.Rational(-3, 2)) == sp.Rational(-1, 3)
    print("  PASS: Lemma 2.3(iv) transverse-slope formula verified across 5 minimal models, layers 0-2.", flush=True)

    # 1b. Allowed vs reflected vs forbidden descent
    cases = [
        ("LY (2,5) (1,2) d=-1/5 allowed", 2, 5, 1, 2, Fraction(-1, 5), True, True, 6),
        ("LY (2,5) (1,2) d=14/5 reflected (regular F_N, fails descent at N=2)", 2, 5, 1, 2, Fraction(14, 5), False, True, 5),
        ("Ising (3,4) (1,2) d=1/2 allowed", 3, 4, 1, 2, Fraction(1, 2), True, True, 6),
        ("Ising (3,4) (1,2) d=1/16 forbidden", 3, 4, 1, 2, Fraction(1, 16), False, False, 4),
        ("(3,5) (1,2) d=1/5 allowed", 3, 5, 1, 2, Fraction(1, 5), True, True, 6),
        ("(3,5) (1,2) d=8/5 half-fusion (kills P_{2,3}, not P_{1,2})", 3, 5, 1, 2, Fraction(8, 5), False, False, 6),
        ("(3,5) (1,3) d=8/5 half-fusion (kills smaller P_{1,3}, not P_{2,2})", 3, 5, 1, 3, Fraction(8, 5), False, False, 5),
        ("Tricrit (4,5) (1,2) d=3/2 half-fusion (kills P_{3,3}, not P_{1,2})", 4, 5, 1, 2, Fraction(3, 2), False, False, 4),
    ]
    for label, p, pp, r, s, d_val, allowed_desc, allowed_reg, maxN in cases:
        c_val = Fraction(1) - Fraction(6 * (pp - p) ** 2, p * pp)
        lam = Fraction((pp * r - p * s) ** 2 - (pp - p) ** 2, 4 * p * pp)
        res = direct_quotient_trace(c_val, lam, d_val, maxN)
        all_desc = all(ok for _, _, ok, _ in res)
        assert all_desc == allowed_desc, f"Descent mismatch on {label}: got {all_desc}"
        l_min = min(r * s, (p - r) * (pp - s))
        l_max = max(r * s, (p - r) * (pp - s))
        set_cd(c_val, d_val)
        ord_min, _ = laurent_trace_Q(dr.gram_matrix(l_min), dr.vertex_matrix(l_min), lam, order=2)
        if allowed_reg:
            ord_max, _ = laurent_trace_Q(dr.gram_matrix(l_max), dr.vertex_matrix(l_max), lam, order=2)
            assert ord_min >= 0 and ord_max >= 0, f"Unexpected pole at {label}: ({ord_min},{ord_max})"
            print(f"  PASS: {label} (desc={all_desc}, ord_x(F_{l_min})={ord_min}, ord_x(F_{l_max})={ord_max})", flush=True)
        else:
            if ord_min == -1:
                print(f"  PASS: {label} (desc={all_desc}, ord_x(F_{l_min})=-1)", flush=True)
            else:
                ord_max, _ = laurent_trace_Q(dr.gram_matrix(l_max), dr.vertex_matrix(l_max), lam, order=2)
                assert ord_min == 0 and ord_max == -1, f"Expected pole at l_max={l_max}, got ({ord_min},{ord_max})"
                print(f"  PASS: {label} (desc={all_desc}, ord_x(F_{l_min})=0, ord_x(F_{l_max})=-1)", flush=True)


# ---------------------------------------------------------------- CHECK 2: Theorem 2

def audit_theorem2():
    print("[2/4] Auditing Theorem 2 (two-weight fusion product rule, rectangle & Gamma potential)...", flush=True)
    # 2a. Two-weight Ward symmetry & f'(0) = 2 p'(0) p_out at generic t = 3/5
    tv = sp.Rational(3, 5)
    cv = 13 + 6 * tv + 6 / tv
    x1, x2 = sp.symbols("x1 x2")

    def h_rs(r, s):
        return ((tv + 1) ** 2 - (r * tv + s) ** 2) / (4 * tv)

    def make_rho2(c_val, d_val):
        @lru_cache(maxsize=None)
        def act_gen(m, word, h_sym):
            if not word:
                return {}
            n, rest = word[0], word[1:]
            out = {}
            for w, poly in act_gen(m, rest, h_sym).items():
                for w2, coef in es.normal_order_negative((n,) + w).items():
                    out[w2] = out.get(w2, 0) + poly * coef
            k = m + n
            if k < 0:
                for w2, coef in es.normal_order_negative((k,) + rest).items():
                    out[w2] = out.get(w2, 0) + (m - n) * coef
            elif k == 0:
                lv = -sum(rest)
                out[rest] = out.get(rest, 0) + (m - n) * (h_sym + lv) + c_val * (m**3 - m) / 12
            else:
                for w2, poly in act_gen(k, rest, h_sym).items():
                    out[w2] = out.get(w2, 0) + (m - n) * poly
            return {w: sp.expand(v) for w, v in out.items() if sp.expand(v) != 0}

        @lru_cache(maxsize=None)
        def rho2(lw, rw, h1, h2):
            if lw:
                m = lw[-1]
                short = lw[:-1]
                wt_l = h1 + sum(short)
                wt_r = h2 - sum(rw)
                res = (wt_l - wt_r + m * d_val) * rho2(short, rw, h1, h2)
                for w, poly in act_gen(m, rw, h2).items():
                    res += poly * rho2(short, w, h1, h2)
                return sp.expand(res)
            if rw:
                m = rw[0]
                short = rw[1:]
                wt_l = h1
                wt_r = h2 - sum(short)
                return sp.expand(-(wt_l - wt_r + m * d_val) * rho2((), short, h1, h2))
            return sp.Integer(1)

        return rho2

    for (R, S, k, m) in [(1, 2, 0, 1), (1, 3, 0, 2), (2, 2, 0, 1), (2, 2, 1, 1)]:
        h0, hout, dv = h_rs(R, S), h_rs(R, -S), h_rs(2 * k + 1, 2 * m + 1)
        B = list(es.partitions(R * S))
        G0 = sp.Matrix([[es.gram_entry(p1, p2).subs({es.c: cv, es.h: h0}) for p2 in B] for p1 in B])
        w = G0.nullspace()[0]

        def compute_deriv(d_test):
            rho2 = make_rho2(cv, d_test)
            f_xx = sp.Integer(0)
            p_x1 = sp.Integer(0)
            p_out = sp.Integer(0)
            for i, a in enumerate(w):
                if a == 0:
                    continue
                lw = tuple(reversed(B[i]))
                rw = tuple(-z for z in B[i])
                p_x1 += a * rho2((), rw, h0 + x1, h0)
                p_out += a * rho2(lw, (), h0, hout)
                for j, b in enumerate(w):
                    if b == 0:
                        continue
                    f_xx += a * b * rho2(lw, tuple(-z for z in B[j]), h0 + x1, h0 + x1)
            df = sp.simplify(sp.diff(f_xx, x1).subs(x1, 0))
            df_prod = sp.simplify(2 * sp.diff(p_x1, x1).subs(x1, 0) * p_out)
            assert sp.simplify(df - df_prod) == 0
            return df

        num = compute_deriv(dv)
        den = compute_deriv(sp.Integer(0))
        got = sp.simplify(num / den)
        # Compare with rectangle formula
        top = {(a, b) for a in range(1 - R + k, R + k + 1) for b in range(1 - S + m, S + m + 1)}
        bot = {(a, b) for a in range(1 - R, R + 1) for b in range(1 - S, S + 1)}
        box = sp.Integer(1)
        for (a, b) in (top - bot):
            box *= (a * tv + b)
        for (a, b) in (bot - top):
            box /= (a * tv + b)
        assert sp.simplify(got - box) == 0, f"Mismatch for {(R, S, k, m)}: {got} vs {box}"
        print(f"  PASS: (R,S)=({R},{S}), (k,m)=({k},{m}): c = {got}", flush=True)

    # 2b. Verify Gamma-potential ratio matches box formula SYMBOLICALLY for indeterminate t!
    t_sym = sp.Symbol("t")
    for (R, S, k, m) in [(1, 2, 0, 1), (1, 3, 0, 2), (2, 2, 1, 1), (2, 3, 1, 1), (3, 3, 2, 2)]:
        top = {(a, b) for a in range(1 - R + k, R + k + 1) for b in range(1 - S + m, S + m + 1)}
        bot = {(a, b) for a in range(1 - R, R + 1) for b in range(1 - S, S + 1)}
        box = sp.Integer(1)
        for (a, b) in (top - bot):
            box *= (a * t_sym + b)
        for (a, b) in (bot - top):
            box /= (a * t_sym + b)
        y_in, y_out = R * t_sym + S, R * t_sym - S
        x_in, x_out = R + S / t_sym, R - S / t_sym
        # Note: (1 + x_in + j/t) - (1 - x_out + j/t) = 2R (integer),
        #       (1 - x_in + j/t) - (1 + x_out + j/t) = -2R (integer),
        #       (1 + y_in + i*t + m) - (1 + y_out + i*t + m) = 2S (integer),
        #       (1 - y_in + i*t + m) - (1 - y_out + i*t + m) = -2S (integer).
        psi_r = sp.Integer(1)
        for j in range(1, m + 1):
            psi_r *= sp.gammasimp(sp.gamma(1 + x_in + j / t_sym) / sp.gamma(1 - x_out + j / t_sym))
            psi_r *= sp.gammasimp(sp.gamma(1 - x_in + j / t_sym) / sp.gamma(1 + x_out + j / t_sym))
        for i in range(1, k + 1):
            psi_r *= sp.gammasimp(sp.gamma(1 + y_in + i * t_sym + m) / sp.gamma(1 + y_out + i * t_sym + m))
            psi_r *= sp.gammasimp(sp.gamma(1 - y_in + i * t_sym + m) / sp.gamma(1 - y_out + i * t_sym + m))
        assert sp.simplify(psi_r - box) == 0, f"Symbolic Gamma mismatch for {(R, S, k, m)}"
    print("  PASS: Symbolic Gamma-potential Psi_{2k+1,2m+1} matches box ratio identically in Q(t) on all 5 shapes.", flush=True)


# ---------------------------------------------------------------- CHECK 3: Theorem 3 (exact Q)

def audit_theorem3_direct():
    print("[3/4] Auditing Theorem 3 (direct quotient-Gram trace == BGG Verma sum in exact Q)...", flush=True)
    # Include Lee-Yang N=0..9 (layer 2!), Ising N=0..8, and Tricritical Ising all 3 fusion weights!
    tests = [
        ("Lee-Yang (2,5) (1,2) d=h_{1,3}=-1/5 [crosses layer 2 at N=9!]", 2, 5, 1, 2, 1, 3, 9),
        ("Ising (3,4) (1,2) d=h_{1,3}=1/2", 3, 4, 1, 2, 1, 3, 8),
        ("Tricritical Ising (4,5) (2,2) d=h_{1,3}=3/5", 4, 5, 2, 2, 1, 3, 7),
        ("Tricritical Ising (4,5) (2,2) d=h_{3,1}=3/2", 4, 5, 2, 2, 3, 1, 7),
        ("Tricritical Ising (4,5) (2,2) d=h_{3,3}=1/10 [two-index]", 4, 5, 2, 2, 3, 3, 7),
    ]
    traces = {}
    for label, p, pp, r, s, u, v, maxN in tests:
        c_val = Fraction(1) - Fraction(6 * (pp - p) ** 2, p * pp)
        lam = Fraction((pp * r - p * s) ** 2 - (pp - p) ** 2, 4 * p * pp)
        d_val = Fraction((pp * u - p * v) ** 2 - (pp - p) ** 2, 4 * p * pp)
        irr = direct_quotient_trace(c_val, lam, d_val, maxN)
        traces[(p, pp, d_val)] = [irr[N][3] for N in range(maxN + 1)]
        terms = bgg_terms(p, pp, r, s, u, v, maxN)
        set_cd(c_val, d_val)
        G_cache = {N: dr.gram_matrix(N) for N in range(maxN + 1)}
        R_cache = {N: dr.vertex_matrix(N) for N in range(maxN + 1)}
        F_vals = {}
        for _, lv, _, _ in terms:
            vals = []
            for M in range(maxN - lv + 1):
                ord_x, cs = laurent_trace_Q(G_cache[M], R_cache[M], lam + lv, order=2)
                assert ord_x >= 0, f"Pole at {label}, lv={lv}, M={M}"
                vals.append(cs[0] if ord_x == 0 else Fraction(0))
            F_vals[lv] = vals
        for N in range(maxN + 1):
            pred = sum(a * F_vals[lv][N - lv] for _, lv, _, a in terms if lv <= N)
            assert pred == irr[N][3], f"Mismatch at {label} N={N}: {pred} vs {irr[N][3]}"
        print(f"  PASS: {label}, N=0..{maxN} exact match ({len(terms)} BGG terms)", flush=True)

    # Tricritical Ising, lambda = 3/80: closed forms of Gaberdiel-Lang (arXiv:0810.0106v2, section 3.4).
    n7 = 7

    def series_mul(a, b):
        return [sum(a[i] * b[n - i] for i in range(n + 1)) for n in range(n7 + 1)]

    def phi_power(a):
        # prod_{n>=1} (1 - q^n)^a via f_n = (1/n) sum_k k g_k f_{n-k}, g_k = -a sigma_1(k)/k
        g = [Fraction(0)] + [-a * Fraction(sum(e for e in range(1, k + 1) if k % e == 0), k)
                             for k in range(1, n7 + 1)]
        f = [Fraction(1)]
        for n in range(1, n7 + 1):
            f.append(sum(k * g[k] * f[n - k] for k in range(1, n + 1)) / n)
        return f

    inv_phi_q2 = [Fraction(0)] * (n7 + 1)  # 1/phi(q^2) = sum_n p(n) q^{2n}
    parts = [1] + [0] * n7
    for k in range(1, n7 + 1):
        for n in range(k, n7 + 1):
            parts[n] += parts[n - k]
    for n in range(0, n7 // 2 + 1):
        inv_phi_q2[2 * n] = Fraction(parts[n])

    # d = 3/2: series solution of (D_{7/2} D_{3/2} - (119/3600) E_4) chi = 0, (3.40), with exponent 1/120,
    # D_k = q d/dq - (k/12) E_2, E_2 = 1 - 24 sum sigma_1(n) q^n, E_4 = 1 + 240 sum sigma_3(n) q^n.
    def sig(k, n):
        return sum(e ** k for e in range(1, n + 1) if n % e == 0)

    e2 = [Fraction(1)] + [Fraction(-24 * sig(1, n)) for n in range(1, n7 + 1)]
    e4 = [Fraction(1)] + [Fraction(240 * sig(3, n)) for n in range(1, n7 + 1)]
    e2sq = series_mul(e2, e2)
    s0 = Fraction(1, 120)
    ode = [Fraction(1)]
    for N in range(1, n7 + 1):
        x = s0 + N
        rest = sum((-Fraction(1, 8) * k * e2[k] - Fraction(5, 12) * e2[k] * (x - k)
                    + Fraction(7, 192) * e2sq[k] - Fraction(119, 3600) * e4[k]) * ode[N - k]
                   for k in range(1, N + 1))
        ode.append(-rest / (x * x - Fraction(5, 12) * x + Fraction(7, 192) - Fraction(119, 3600)))

    closed = {
        Fraction(1, 10): ("phi(q)^(1/5)", phi_power(Fraction(1, 5))),
        Fraction(3, 5): ("phi(q)^(11/5)/phi(q^2)", series_mul(phi_power(Fraction(11, 5)), inv_phi_q2)),
        Fraction(3, 2): ("series solution of Gaberdiel-Lang (3.40)", ode),
    }
    for d_val, (name, ser) in closed.items():
        assert traces[(4, 5, d_val)] == ser, f"Tricritical closed-form mismatch at d={d_val}"
        print(f"  PASS: Tricritical Ising (4,5) lambda=3/80 d={d_val} trace equals {name} for N=0..{n7}", flush=True)
    g_vac = series_mul(ode, phi_power(Fraction(-3)))
    assert g_vac[:6] == [1, 14, 42, 140, 350, 840], "d=3/2 trace / phi^3 differs from Gaberdiel-Lang's printed series"
    print(f"  PASS: d=3/2 trace / phi(q)^3 = {[int(x) for x in g_vac]} (Gaberdiel-Lang print 1, 14, 42, 140, 350, 840)", flush=True)


# ---------------------------------------------------------------- CHECK 4: Corollary 1 (collision-free)

def audit_corollary_collision_free(maxN_ising, maxN_ly):
    print(f"[4/4] Auditing Corollary 1 (collision-free single-index recursion: Ising N<={maxN_ising}, LY N<={maxN_ly})...", flush=True)

    def run_single_index(p, pp, r, s, m_ext, maxN):
        t = Fraction(-pp, p)
        Q2 = t + 2 + Fraction(1) / t
        v_ext = 2 * m_ext + 1
        mom_d2 = t + 2 * v_ext + Fraction(v_ext * v_ext) / t

        def kac_h(R, S):
            return (Q2 - (R * R * t + 2 * R * S + Fraction(S * S) / t)) / 4

        @lru_cache(maxsize=None)
        def res_RS(R, S):
            den = Fraction(2)
            for a in range(1 - R, R + 1):
                for bp in range(1 - S, S + 1):
                    if (a, bp) in ((0, 0), (R, S)):
                        continue
                    den *= (a * t + bp)
            A = (t ** (2 * R * S - 1)) / den
            tau = Fraction(1)
            for k in range(1, 2 * R, 2):
                for ell in range(1, 2 * S, 2):
                    tau *= (mom_d2 - (k * k * t + 2 * k * ell + Fraction(ell * ell) / t)) / 4
                    tau *= (mom_d2 - (k * k * t - 2 * k * ell + Fraction(ell * ell) / t)) / 4
            return A * tau

        active = [(R, S) for S in range(1, m_ext + 1) for R in range(1, maxN // S + 1)]

        @lru_cache(maxsize=None)
        def H_shifted(R, S, lv):
            if lv == 0:
                return Fraction(1)
            h_src = kac_h(R, S) + R * S
            tot = Fraction(0)
            for (u, v) in active:
                if u * v > lv:
                    continue
                tot += res_RS(u, v) * H_shifted(u, v, lv - u * v) / (h_src - kac_h(u, v))
            return tot

        def H_at(h_val, maxL):
            out = [Fraction(1)]
            for N in range(1, maxL + 1):
                tot = Fraction(0)
                for (u, v) in active:
                    if u * v > N:
                        continue
                    tot += res_RS(u, v) * H_shifted(u, v, N - u * v) / (h_val - kac_h(u, v))
                out.append(tot)
            return out

        pnum = [0] * (maxN + 1)
        pnum[0] = 1
        for k in range(1, maxN + 1):
            for n in range(k, maxN + 1):
                pnum[n] += pnum[n - k]

        def H_to_F(H):
            return [sum(H[i] * pnum[N - i] for i in range(N + 1)) for N in range(len(H))]

        lam = Fraction((pp * r - p * s) ** 2 - (pp - p) ** 2, 4 * p * pp)
        terms = bgg_terms(p, pp, r, s, 1, v_ext, maxN)
        T = [Fraction(0)] * (maxN + 1)
        for _, lv, _, a in terms:
            F = H_to_F(H_at(lam + lv, maxN - lv))
            for M in range(len(F)):
                T[lv + M] += a * F[M]
        return T, terms

    # Ising: compare with Euler pentagonal product phi(q) = prod_{n>=1} (1 - q^n)
    T_ising, terms_i = run_single_index(3, 4, 1, 2, 1, maxN_ising)
    phi = [0] * (maxN_ising + 1)
    for k in range(-20, 21):
        e = k * (3 * k - 1) // 2
        if 0 <= e <= maxN_ising:
            phi[e] += (-1) ** k
    for N in range(maxN_ising + 1):
        assert T_ising[N] == phi[N], f"Ising mismatch at N={N}: {T_ising[N]} vs {phi[N]}"
    print(f"  PASS: Ising (3,4) (1,2) d=1/2 matches Euler phi(q) for all N=0..{maxN_ising} ({len(terms_i)} BGG terms)", flush=True)

    # Lee-Yang: cross-check against direct quotient-Gram for N<=9 and pure 5-power denominators up to maxN_ly
    T_ly, terms_ly = run_single_index(2, 5, 1, 2, 1, maxN_ly)
    irr_ly = direct_quotient_trace(Fraction(-22, 5), Fraction(-1, 5), Fraction(-1, 5), min(9, maxN_ly))
    for N in range(min(9, maxN_ly) + 1):
        assert T_ly[N] == irr_ly[N][3], f"LY mismatch at N={N}"

    def is_pow5(n):
        while n % 5 == 0:
            n //= 5
        return n == 1

    assert all(is_pow5(x.denominator) for x in T_ly)

    # Closed form: phi(q)^(-2/5) = prod_{n>=1} (1 - q^n)^(-2/5), via log-derivative recursion
    # f_n = (1/n) sum_{k=1}^n k g_k f_{n-k}, with g_k = (2/5) sigma(k)/k the coefficients of log f.
    a = Fraction(-2, 5)
    g = [Fraction(0)] + [-a * Fraction(sum(e for e in range(1, k + 1) if k % e == 0), k)
                         for k in range(1, maxN_ly + 1)]
    f = [Fraction(1)]
    for n in range(1, maxN_ly + 1):
        f.append(sum(k * g[k] * f[n - k] for k in range(1, n + 1)) / n)
    for N in range(maxN_ly + 1):
        assert T_ly[N] == f[N], f"LY closed-form mismatch at N={N}: {T_ly[N]} vs {f[N]}"
    print(f"  PASS: Lee-Yang (2,5) (1,2) d=-1/5 matches direct quotient-Gram N<=9, equals phi(q)^(-2/5) and has pure 5-power denominators for all N=0..{maxN_ly} ({len(terms_ly)} BGG terms)", flush=True)


def main():
    parser = argparse.ArgumentParser(
        description="Exact rational and symbolic audit for irreducible minimal-model torus one-point traces."
    )
    parser.add_argument("--max-ising", type=int, default=30, help="Max level for Ising collision-free recursion audit (default: 30)")
    parser.add_argument("--max-ly", type=int, default=25, help="Max level for Lee-Yang collision-free recursion audit (default: 25)")
    args = parser.parse_args()

    audit_theorem1()
    audit_theorem2()
    audit_theorem3_direct()
    audit_corollary_collision_free(args.max_ising, args.max_ly)
    print("ALL IRREDUCIBLE TORUS AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
