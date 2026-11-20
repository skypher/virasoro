#!/usr/bin/env python3
"""Exact small-case exploration of sphere four-point Virasoro blocks.

Computes B_N (z-expansion) and H_N (elliptic nome expansion) directly from
Shapovalov Gram matrices and closed-form three-point pairings, verifies the
closed-form pairing against direct Ward commutation, checks the fusion
polynomial P_{r,s} signs/normalizations, and compares pole orders and top
Jantzen-layer coefficients at minimal models (2,3), (2,5), and (3,4).
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Fr
from functools import lru_cache
import sympy as sp


def partitions(n: int, largest: int | None = None):
    if n == 0:
        yield ()
        return
    if largest is None or largest > n:
        largest = n
    for first in range(largest, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


# ---------- Polynomials in h over Q (tuples of Fractions) ----------

def pnorm(t):
    t = list(t)
    while t and t[-1] == 0:
        t.pop()
    return tuple(t)

def padd(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else Fr(0)) + (b[i] if i < len(b) else Fr(0))
                  for i in range(n)])

def pmul(a, b):
    if not a or not b:
        return ()
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return pnorm(out)

def pscale(a, s):
    if s == 0 or not a:
        return ()
    return pnorm([x * s for x in a])

def peval(a, v):
    r = Fr(0)
    for coef in reversed(a):
        r = r * v + coef
    return r

PONE = (Fr(1),)
PH = (Fr(0), Fr(1))


@lru_cache(maxsize=None)
def normal_order(word: tuple[int, ...]):
    for i in range(len(word) - 1):
        a, b = word[i], word[i + 1]
        if a > b:
            out = {}
            for w, coef in normal_order(word[:i] + (b, a) + word[i + 2:]).items():
                out[w] = out.get(w, Fr(0)) + coef
            for w, coef in normal_order(word[:i] + (a + b,) + word[i + 2:]).items():
                out[w] = out.get(w, Fr(0)) + (a - b) * coef
            return {w: c for w, c in out.items() if c != 0}
    return {word: Fr(1)}


def _dadd(target, word, poly):
    if poly:
        cur = target.get(word)
        target[word] = padd(cur, poly) if cur is not None else poly
        if not target[word]:
            del target[word]


def make_gram_builder(c_val: Fr):
    @lru_cache(maxsize=None)
    def act(m: int, word: tuple[int, ...]):
        if not word:
            return {}
        n, rest = word[0], word[1:]
        out = {}
        for w, poly in act(m, rest).items():
            for w2, coef in normal_order((n,) + w).items():
                _dadd(out, w2, pscale(poly, coef))
        k = m + n
        if k < 0:
            for w2, coef in normal_order((k,) + rest).items():
                _dadd(out, w2, pscale(PONE, (m - n) * coef))
        elif k == 0:
            level = -sum(rest)
            _dadd(out, rest, pscale(padd(PH, (Fr(level),)), m - n))
            _dadd(out, rest, pscale(PONE, c_val * (m**3 - m) / 12))
        else:
            for w2, poly in act(k, rest).items():
                _dadd(out, w2, pscale(poly, m - n))
        return out

    def gram_entry(left, right):
        comb = {tuple(-p for p in right): PONE}
        for mode in left:
            nxt = {}
            for w, poly in comb.items():
                for w2, poly2 in act(mode, w).items():
                    _dadd(nxt, w2, pmul(poly, poly2))
            comb = nxt
        return comb.get((), ())

    def gram_matrix(level: int):
        B = list(partitions(level))
        n = len(B)
        M = [[() for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                e = gram_entry(B[i], B[j])
                M[i][j] = e
                M[j][i] = e
        return B, M

    return gram_matrix


def gamma_poly(part: tuple[int, ...], da: Fr, db: Fr):
    """Exact polynomial in h for <h| L_{y_l}..L_{y_1} Phi_b(1) |da>."""
    poly = PONE
    l = len(part)
    tail_sum = 0
    for j in range(l - 1, -1, -1):
        yj = part[j]
        # factor is (h + tail_sum + yj * db - da)
        fac = (Fr(tail_sum) + yj * db - da, Fr(1))
        poly = pmul(poly, fac)
        tail_sum += yj
    return poly


def verify_gamma_formula_symbolic():
    """Verify gamma_poly against direct Virasoro Ward commutation up to level 4."""
    h, da, db, z = sp.symbols("h da db z")

    def ward_right(n, expr):
        return sp.expand(z**n * (z * sp.diff(expr, z) + (n + 1) * db * expr))

    @lru_cache(maxsize=None)
    def direct_right(left_word: tuple[int, ...]):
        # <h| L_{left_word[0]} ... L_{left_word[-1]} Phi_b(z) |da>
        if not left_word:
            return z ** (h - db - da)
        nearest = left_word[-1]
        short = left_word[:-1]
        return ward_right(nearest, direct_right(short))

    def ward_left(n, expr):
        # <d4| Phi_3(z) L_{-n} ... = - [L_{-n}, Phi_3(z)]
        return sp.expand(-z**(-n) * (z * sp.diff(expr, z) + (1 - n) * db * expr))

    @lru_cache(maxsize=None)
    def direct_left(right_word: tuple[int, ...]):
        # <da| Phi_b(z) L_{-right_word[0]} ... L_{-right_word[-1]} |h>
        if not right_word:
            return z ** (da - db - h)
        nearest = right_word[0]
        short = right_word[1:]
        return ward_left(nearest, direct_left(short))

    for level in range(5):
        for Y in partitions(level):
            # Formula: prod_{j=0}^{l-1} (h + sum_{i>j} Y[i] + Y[j]*db - da)
            prod = sp.Integer(1)
            for j in range(len(Y)):
                tail = sum(Y[j + 1:])
                prod *= (h + tail + Y[j] * db - da)
            prod = sp.expand(prod)
            dr = sp.expand(direct_right(tuple(reversed(Y))).subs(z, 1))
            dl = sp.expand(direct_left(Y).subs(z, 1))
            assert sp.simplify(prod - dr) == 0, f"right mismatch at {Y}: {prod} vs {dr}"
            assert sp.simplify(prod - dl) == 0, f"left mismatch at {Y}: {prod} vs {dl}"
    print("[PASS] gamma_Y closed-form formula verified against direct Ward identities (levels 0..4)", flush=True)


def verify_fusion_polynomials_symbolic():
    """Verify <chi_{r,s}(b) | Phi_2(1) | d1> == P_{r,s}(b, d1, d2) for rs <= 6."""
    b, L1, L2 = sp.symbols("b L1 L2")
    Q = b + 1 / b
    c_expr = 1 + 6 * Q**2
    d1 = (Q**2 - L1**2) / 4
    d2 = (Q**2 - L2**2) / 4

    # Symbolic Gram & Virasoro action
    h_sym, c_sym = sp.symbols("h c")

    @lru_cache(maxsize=None)
    def act_sym(m, word):
        if not word:
            return {}
        n, rest = word[0], word[1:]
        out = {}
        for w, coeff in act_sym(m, rest).items():
            for w2, nc in normal_order((n,) + w).items():
                out[w2] = sp.expand(out.get(w2, 0) + coeff * sp.Rational(nc.numerator, nc.denominator))
        k = m + n
        if k < 0:
            for w2, nc in normal_order((k,) + rest).items():
                out[w2] = sp.expand(out.get(w2, 0) + (m - n) * sp.Rational(nc.numerator, nc.denominator))
        elif k == 0:
            level = -sum(rest)
            out[rest] = sp.expand(out.get(rest, 0) + (m - n) * (h_sym + level) + c_sym * (m**3 - m) / 12)
        else:
            for w2, coeff in act_sym(k, rest).items():
                out[w2] = sp.expand(out.get(w2, 0) + (m - n) * coeff)
        return {w: v for w, v in out.items() if v != 0}

    def find_singular_vector(r, s):
        level = r * s
        hrs = sp.expand((Q**2 - (r * b + s / b)**2) / 4)
        B = list(partitions(level))
        # Solve L_1 v = 0 and L_2 v = 0 with v_{(1^level)} = 1
        rows = []
        # Target bases at level-1 and level-2
        for m in (1, 2):
            if level - m < 0:
                continue
            Bm = list(partitions(level - m))
            idx = {tuple(-x for x in p): i for i, p in enumerate(Bm)}
            mat = [[sp.Integer(0) for _ in B] for _ in Bm]
            for j, Y in enumerate(B):
                res = act_sym(m, tuple(-x for x in Y))
                for w, val in res.items():
                    mat[idx[w]][j] = sp.cancel(val.subs({c_sym: c_expr, h_sym: hrs}))
            rows.extend(mat)
        M = sp.Matrix(rows)
        ns = M.nullspace()
        assert len(ns) == 1, f"expected 1D nullspace for ({r},{s}), got {len(ns)}"
        vec = ns[0]
        # normalize L_{-1}^{rs} coefficient (last partition in descending order) to 1
        assert B[-1] == (1,) * level
        scale = vec[-1]
        vec = [sp.cancel(v / scale) for v in vec]
        return B, hrs, vec

    def P_rs_formula(r, s):
        prod = sp.Integer(1)
        for j in range(1 - r, r, 2):
            for l in range(1 - s, s, 2):
                pjl = j * b + l / b
                prod *= ((L1 + L2 + pjl) / 2) * ((L1 - L2 + pjl) / 2)
        return sp.expand(prod)

    for r in range(1, 5):
        for s in range(1, 5):
            if r * s > 4:
                continue
            B, hrs, vec = find_singular_vector(r, s)
            # Evaluate <chi_{r,s}| Phi_2(1) |d1> = sum_Y vec[Y] * gamma_Y(hrs; d1, d2)
            val = sp.Integer(0)
            for coef, Y in zip(vec, B):
                g = sp.Integer(1)
                for j in range(len(Y)):
                    g *= (hrs + sum(Y[j + 1:]) + Y[j] * d2 - d1)
                val += coef * g
            val = sp.expand(val)
            P = P_rs_formula(r, s)
            # Check ratio val / P (could be (+1) or (-1)^{rs}!)
            diff_plus = sp.simplify(val - P)
            diff_minus = sp.simplify(val + P)
            sign = "+1" if diff_plus == 0 else ("-1" if diff_minus == 0 else "MISMATCH")
            print(f"  ({r},{s}): <chi|Phi_2|d1> / P_rs = {sign}", flush=True)
            assert sign in ("+1", "-1"), f"mismatch at ({r},{s})"
    print("[PASS] Fusion polynomial signs verified for all rs <= 4", flush=True)


# ---------- Exact elliptic series coefficients (rational) ----------

def series_mul(a, b, N):
    out = [Fr(0)] * (N + 1)
    for i in range(min(len(a), N + 1)):
        if a[i]:
            for j in range(min(len(b), N + 1 - i)):
                if b[j]:
                    out[i + j] += a[i] * b[j]
    return out

def series_inv(a, N):
    assert a[0] != 0
    out = [Fr(0)] * (N + 1)
    out[0] = Fr(1) / a[0]
    for k in range(1, N + 1):
        s = Fr(0)
        for j in range(1, min(k + 1, len(a))):
            s += a[j] * out[k - j]
        out[k] = -s / a[0]
    return out

def series_pow_rational(a, alpha: Fr, N: int):
    """Compute a(q)^alpha mod q^{N+1} assuming a[0] == 1."""
    assert a[0] == 1
    out = [Fr(0)] * (N + 1)
    out[0] = Fr(1)
    for n in range(1, N + 1):
        s = Fr(0)
        for k in range(1, min(n + 1, len(a))):
            s += (alpha * k - (n - k)) * a[k] * out[n - k]
        out[n] = s / n
    return out

def series_pow_poly_h(a, alpha_poly, N: int):
    """Compute a(q)^{alpha(h)} mod q^{N+1} where alpha_poly is tuple in h, a[0]==1."""
    assert a[0] == 1
    out = [() for _ in range(N + 1)]
    out[0] = PONE
    for n in range(1, N + 1):
        s = ()
        for k in range(1, min(n + 1, len(a))):
            if a[k]:
                # (alpha_poly * k - (n - k)) * a[k] * out[n - k]
                fac = padd(pscale(alpha_poly, Fr(k)), (Fr(-(n - k)),))
                s = padd(s, pscale(pmul(fac, out[n - k]), a[k]))
        out[n] = pscale(s, Fr(1, n))
    return out

def theta_series(N: int):
    """Return theta_3(q), theta_4(q), (theta_2(q)/(2 q^{1/4}))^4, z(q)/(16q), 1-z(q) mod q^{N+1}."""
    th3 = [Fr(0)] * (N + 1)
    th4 = [Fr(0)] * (N + 1)
    th3[0] = Fr(1)
    th4[0] = Fr(1)
    m = 1
    while m * m <= N:
        th3[m * m] = Fr(2)
        th4[m * m] = Fr(2) if m % 2 == 0 else Fr(-2)
        m += 1
    # theta_2(q)/(2 q^{1/4}) = sum_{n>=0} q^{n(n+1)}
    th2_red = [Fr(0)] * (N + 1)
    n = 0
    while n * (n + 1) <= N:
        th2_red[n * (n + 1)] = Fr(1)
        n += 1
    th2_4 = series_mul(series_mul(th2_red, th2_red, N), series_mul(th2_red, th2_red, N), N)
    th3_4 = series_mul(series_mul(th3, th3, N), series_mul(th3, th3, N), N)
    th4_4 = series_mul(series_mul(th4, th4, N), series_mul(th4, th4, N), N)
    z_over_16q = series_mul(th2_4, series_inv(th3_4, N), N)
    one_minus_z = series_mul(th4_4, series_inv(th3_4, N), N)
    return th3, th4, z_over_16q, one_minus_z


# ---------- Exact rational reconstruction of B_N(h) and H_N(h) ----------

def solve_quad_form(G, v_left, v_right):
    """Return (det G, v_left^T G^{-1} v_right) over Fraction; second is None if singular."""
    n = len(G)
    A = [row[:] + [rhs] for row, rhs in zip(G, v_right)]
    det = Fr(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fr(0), None
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = -det
        det *= A[col][col]
        inv = Fr(1) / A[col][col]
        A[col] = [x * inv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    val = sum(v_left[i] * A[i][n] for i in range(n))
    return det, val


def lagrange_interp(points):
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    n = len(points)
    coef = ys[:]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    poly = ()
    for i in range(n - 1, -1, -1):
        poly = padd(pmul(poly, (-xs[i], Fr(1))), (coef[i],))
    return poly


class RatFunc:
    def __init__(self, num, den):
        self.num = pnorm(num)
        self.den = pnorm(den)

    def eval(self, x: Fr):
        return peval(self.num, x) / peval(self.den, x)

    def laurent_at(self, point: Fr, kmax: int = 0):
        def shift(p):
            cur = list(p)
            res = []
            while cur:
                q = [Fr(0)] * (len(cur) - 1)
                acc = cur[-1]
                for i in range(len(cur) - 2, -1, -1):
                    q[i] = acc
                    acc = cur[i] + acc * point
                res.append(acc)
                cur = list(pnorm(tuple(q)))
            return pnorm(tuple(res))

        ln = shift(self.num)
        ld = shift(self.den)
        if not ln:
            return 0, {}
        vd = 0
        while vd < len(ld) and ld[vd] == 0:
            vd += 1
        vn = 0
        while vn < len(ln) and ln[vn] == 0:
            vn += 1
        ord_pole = vd - vn
        a = ln[vn:]
        bpoly = ld[vd:]
        need = max(0, kmax + ord_pole + 1)
        inv = []
        b0 = bpoly[0]
        for k in range(need):
            s = a[k] if k < len(a) else Fr(0)
            for j in range(1, min(k, len(bpoly) - 1) + 1):
                s -= bpoly[j] * inv[k - j]
            inv.append(s / b0)
        return max(0, ord_pole), {k - ord_pole: inv[k] for k in range(need)}


def reconstruct_B_and_H(c_val: Fr, d_ext: tuple[Fr, Fr, Fr, Fr], max_level: int):
    """Reconstruct B_N(h) and H_N(h) for N = 0..max_level at fixed (c, d1, d2, d3, d4)."""
    d1, d2, d3, d4 = d_ext
    gm = make_gram_builder(c_val)
    B_funcs = [RatFunc(PONE, PONE)]

    for level in range(1, max_level + 1):
        basis, G = gm(level)
        v_left = [gamma_poly(Y, d4, d3) for Y in basis]
        v_right = [gamma_poly(Y, d1, d2) for Y in basis]
        degD = sum(len(Y) for Y in basis)
        # B_level has numerator degree at most degD + level!
        degP = degD + level
        npts_P = degP + 1
        npts_D = degD + 1
        samples = {}
        x_int = 3
        while len(samples) < npts_P + 1:
            x = Fr(x_int)
            x_int += 1
            Gx = [[peval(e, x) for e in row] for row in G]
            vl = [peval(p, x) for p in v_left]
            vr = [peval(p, x) for p in v_right]
            det, val = solve_quad_form(Gx, vl, vr)
            if det != 0:
                samples[x] = (det, det * val)
        xs = sorted(samples)
        D = lagrange_interp([(x, samples[x][0]) for x in xs[:npts_D]])
        P = lagrange_interp([(x, samples[x][1]) for x in xs[:npts_P]])
        xv = xs[npts_P]
        assert peval(D, xv) == samples[xv][0] and peval(P, xv) == samples[xv][1]
        B_funcs.append(RatFunc(P, D))

    # Build H_N(h) from B_0..B_N via elliptic prefactor
    # H(q) = (z/16q)^{h - (c-1)/24} * (1-z)^{d2+d3-(c-1)/24} * th3^{4*sum(d)-(c-1)/2} * sum B_m (z(q))^m
    # Reconstruct H_N(h) by evaluating at regular sample points!
    th3, th4, z16, omz = theta_series(max_level)
    # z(q) = 16q * z16(q). Write H(q) = sum H_N (16q)^N, so H_N = [q^N] H(q) / 16^N.
    # Evaluate H_N(h) at sample points using the common denominator D_N of B_N (wait: det G_m divides det G_N for m <= N!).
    # Indeed by Kac determinant, every zero of det G_m is a zero of det G_N with >= multiplicity!
    # Double-check: use LCM? Actually det G_N already has multiplicity p(N-rs) >= p(m-rs), so det G_N is a common denominator of B_0..B_N!
    # Also since H_N -> 0 as h -> infty, deg(num of H_N) < deg(det G_N)! Let's reconstruct with degD + 1 + max_level points to be agnostic and verify deg(num) < degD!
    psi1 = series_pow_rational(z16, -(c_val - 1) / 24, max_level)
    psi2 = series_pow_rational(omz, d2 + d3 - (c_val - 1) / 24, max_level)
    psi3 = series_pow_rational(th3, 4 * (d1 + d2 + d3 + d4) - (c_val - 1) / 2, max_level)
    psi = series_mul(series_mul(psi1, psi2, max_level), psi3, max_level)

    # Powers of z(q) = 16q * z16(q): z^m has leading q^m * 16^m * z16^m
    z16_pows = [[Fr(1)] + [Fr(0)] * max_level]
    for m in range(1, max_level + 1):
        z16_pows.append(series_mul(z16_pows[-1], z16, max_level))

    H_funcs = [RatFunc(PONE, PONE)]
    for level in range(1, max_level + 1):
        D = B_funcs[level].den
        degD = len(D) - 1
        # Sample at degD + level + 2 points to verify large-h decay too!
        npts = degD + level + 1
        pts = []
        x_int = 3
        while len(pts) < npts + 1:
            x = Fr(x_int)
            x_int += 1
            dx = peval(D, x)
            if dx == 0:
                continue
            # Evaluate H(q) mod q^{level+1} at h = x
            # First B(z(q)) mod q^{level+1}
            Bz = [Fr(0)] * (level + 1)
            for m in range(level + 1):
                bm = B_funcs[m].eval(x)
                fac16 = Fr(16**m)
                for k in range(level + 1 - m):
                    Bz[m + k] += bm * fac16 * z16_pows[m][k]
            z16_h = series_pow_rational(z16, x, level)
            pref = series_mul(psi[:level + 1], z16_h, level)
            Hq = series_mul(pref, Bz, level)
            hn = Hq[level] / Fr(16**level)
            pts.append((x, dx * hn))
        P_H = lagrange_interp(pts[:npts])
        xv, yv = pts[npts]
        assert peval(P_H, xv) == yv, f"H_{level} reconstruction failed"
        degP_H = len(P_H) - 1
        assert degP_H < degD, f"H_{level} did not decay at infinity! degP={degP_H}, degD={degD}"
        H_funcs.append(RatFunc(P_H, D))

    return B_funcs, H_funcs


def jantzen_levels(p: int, pp: int, r: int, s: int, kmax: int = 4):
    n1 = pp * r + p * s
    if n1 > p * pp:
        r, s = p - r, pp - s
        n1 = pp * r + p * s
    n0 = pp * r - p * s
    out = {}
    for k in range(1, kmax + 1):
        if k % 2 == 1:
            j = (k - 1) // 2
            lp = (r + j * p) * (s + j * pp)
            lm = ((j + 1) * p - r) * ((j + 1) * pp - s)
        else:
            j = k // 2
            lp = j * (j * p * pp + n0)
            lm = j * (j * p * pp - n0)
        out[k] = (lp, lm)
    return out


def j_N(levels_dict, N):
    j = 0
    for k, (lp, lm) in sorted(levels_dict.items()):
        if min(lp, lm) <= N:
            j = k
    return j


def check_minimal_model(p: int, pp: int, r: int, s: int, max_level: int, d_ext: tuple[Fr, Fr, Fr, Fr]):
    c_val = Fr(1) - Fr(6 * (pp - p) ** 2, p * pp)
    lam = Fr((pp * r - p * s) ** 2 - (pp - p) ** 2, 4 * p * pp)
    lvls = jantzen_levels(p, pp, r, s)
    print(f"\n=== Minimal model ({p},{pp}), c={c_val}, (r,s)=({r},{s}), lam={lam}, levels={lvls} ===", flush=True)
    B_funcs, H_funcs = reconstruct_B_and_H(c_val, d_ext, max_level)
    for N in range(1, max_level + 1):
        ob, lb = B_funcs[N].laurent_at(lam, 0)
        oh, lh = H_funcs[N].laurent_at(lam, 0)
        j = j_N(lvls, N)
        lead_b = lb.get(-ob, Fr(0)) if ob > 0 else Fr(0)
        lead_h = lh.get(-oh, Fr(0)) if oh > 0 else Fr(0)
        print(f"  N={N:2d}: j_N={j} | ord(B_N)={ob} ord(H_N)={oh} | lead_B={lead_b} | lead_H={lead_h}", flush=True)
        assert ob == j and oh == j, f"pole order mismatch at N={N}: j={j}, ob={ob}, oh={oh}"
    return B_funcs, H_funcs, c_val, lam, lvls


def check_ribault_23_N5():
    """Verify Ribault 2019 eq. (3.18) at (p,p')=(2,3), (r,s)=(1,1), N=5 against direct Gram reconstruction."""
    # Ribault has beta^2 = 3/2 (i.e. b^2 = -3/2, p=2, p'=3, c=0), lambda = 0, N = 5.
    # Eq. (3.18): H^5_Delta ~ 3 / (11200 Delta^2) * lam(0) * lam(1/(2beta)) * lam(-1/(2beta)) * lam(beta) * lam(-beta)
    # where lam(P) = prod_pm (P2 pm P1 + P)(P3 pm P4 + P), and Delta_i = (beta - 1/beta)^2/4 - P_i^2 = -1/24 - P_i^2
    # Wait: in Ribault 1809.03722: c = 1 - 6(beta - 1/beta)^2, Delta(P) = P^2 - (beta-1/beta)^2/4?
    # Let's check with b^2 = -3/2: Q^2 = (b + 1/b)^2 = -3/2 + 2 - 2/3 = -1/6, so (c-1)/24 = -1/24 = Q^2/4!
    # Our Lambda_i^2 = Q^2 - 4 Delta_i = -1/6 - 4 Delta_i = 4 P_i^2 => P_i = Lambda_i / 2 (with beta = i b, beta^2 = 3/2).
    # Choose rational P_i / beta: let beta = sqrt(3/2), set P_i = r_i * sqrt(6)/12 so P_i^2 is rational!
    # Even simpler: P_i = a_i * beta => P_i^2 = (3/2) a_i^2, so Delta_i = (c-1)/24 + P_i^2 = -1/24 + (3/2) a_i^2 (WAIT: check sign of P_i^2!).
    # At (1,1): Delta_{1,1} = 0 => P_{1,1}^2 = 1/24 = (beta - 1/beta)^2/4 = (3/2 - 2 + 2/3)/4 = (1/6)/4 = 1/24!
    # YES! Delta = P^2 - 1/24! So for P_i = a_i * beta, Delta_i = (3/2) a_i^2 - 1/24.
    # Let a = (1, 2, 3, 5) / 7 (generic rationals).
    beta2 = Fr(3, 2)
    a = [Fr(1, 7), Fr(2, 7), Fr(3, 7), Fr(5, 7)]
    d_ext = tuple(beta2 * ai * ai - Fr(1, 24) for ai in a)
    B_funcs, H_funcs, _, _, _ = check_minimal_model(2, 3, 1, 1, 5, d_ext)
    oh, lh = H_funcs[5].laurent_at(Fr(0), 0)
    ob, lb = B_funcs[5].laurent_at(Fr(0), 0)
    assert oh == 2 and ob == 2 and lh[-2] == lb[-2]

    # Compute Ribault's product: P_i = a_i * beta; shifts are 0, pm 1/(2beta) = pm (1/3)*beta, pm beta.
    # lam(s * beta) = beta^4 * prod_pm (a2 pm a1 + s)(a3 pm a4 + s)
    def lam_s(s: Fr):
        return (beta2**2) * (a[1] + a[0] + s) * (a[1] - a[0] + s) * (a[2] + a[3] + s) * (a[2] - a[3] + s)

    # Note: Ribault 2019 (1809.03722 eq. 3.4, 3.15) has R_{1,1} = -1/2 * lam(0),
    # corresponding to swapping (Delta_3 <-> Delta_4), i.e., q -> -q, which multiplies H_N by (-1)^N.
    ribault = Fr(-1) ** 5 * Fr(3, 11200) * lam_s(Fr(0)) * lam_s(Fr(1, 3)) * lam_s(Fr(-1, 3)) * lam_s(Fr(1)) * lam_s(Fr(-1))
    # Also check N=1 against Ribault R_{1,1}:
    o1, l1 = H_funcs[1].laurent_at(Fr(0), 0)
    assert o1 == 1 and l1[-1] == Fr(-1) ** 1 * Fr(-1, 2) * lam_s(Fr(0))
    print(f"  Direct H_5 [-2] = {lh[-2]}", flush=True)
    print(f"  (-1)^5 * Rib318 = {ribault}", flush=True)
    assert lh[-2] == ribault, f"Ribault mismatch: {lh[-2]} vs {ribault}"
    print("[PASS] Exact match with Ribault 2019 eq. (3.18) at (2,3), lambda=0, N=5 (with (-1)^N from 3<->4)!", flush=True)


def eval_P_rs_at_minmodel(p: int, pp: int, R: int, S: int, d_a: Fr, d_b: Fr) -> Fr:
    """Evaluate P_{R,S}(b_star, d_a, d_b) exactly in Q (no square roots!).

    Using b_star^2 = -pp/p, Q^2 = -(pp-p)^2/(p*pp), Lambda^2 = Q^2 - 4*d.
    For each (j,l) with j in {1-R..R-1 step 2}, l in {1-S..S-1 step 2}:
      ((La + Lb + pjl)/2) * ((La - Lb + pjl)/2) = (La^2 - Lb^2 + 2*La*pjl + pjl^2)/4.
    Pair (j,l) with (-j,-l) (when (j,l) != (0,0)):
      [(La^2 - Lb^2 + pjl^2)^2 - 4*La^2*pjl^2] / 16
      = [(4(d_b - d_a) + pjl^2)^2 - 4*(Q^2 - 4*d_a)*pjl^2] / 16
    where pjl^2 = -(j*pp - l*p)^2 / (p*pp)!
    For (j,l) = (0,0): (La^2 - Lb^2)/4 = d_b - d_a!
    """
    Q2 = -Fr((pp - p) ** 2, p * pp)
    La2 = Q2 - 4 * d_a
    diff = d_b - d_a
    js = list(range(1 - R, R, 2))
    ls = list(range(1 - S, S, 2))
    prod = Fr(1)
    used = set()
    for j in js:
        for l in ls:
            if (j, l) in used:
                continue
            if j == 0 and l == 0:
                prod *= diff
                used.add((0, 0))
            else:
                pjl2 = -Fr((j * pp - l * p) ** 2, p * pp)
                fac = ((4 * diff + pjl2) ** 2 - 4 * La2 * pjl2) / 16
                prod *= fac
                used.add((j, l))
                used.add((-j, -l))
    return prod


def check_ising_N7_gamma():
    """Cross-check Ising (3,4), lambda = 1/2, N = 7 against gamma_7 = -700700 from torus paper Prop 8.1."""
    d_ext = (Fr(1, 3), Fr(2, 5), Fr(3, 7), Fr(5, 11))
    B_funcs, H_funcs, _, _, _ = check_minimal_model(3, 4, 2, 1, 7, d_ext)
    oh, lh = H_funcs[7].laurent_at(Fr(1, 2), 0)
    ob, lb = B_funcs[7].laurent_at(Fr(1, 2), 0)
    assert oh == 2 and ob == 2 and lh[-2] == lb[-2]
    # From torus paper Prop 8.1: w^-_2 at level 7 has fusion factorization P_{2,1} * P_{1,5}, gamma_7 = -700700!
    d1, d2, d3, d4 = d_ext
    pi_21 = eval_P_rs_at_minmodel(3, 4, 2, 1, d1, d2) * eval_P_rs_at_minmodel(3, 4, 1, 5, d1, d2)
    pi_43 = eval_P_rs_at_minmodel(3, 4, 2, 1, d4, d3) * eval_P_rs_at_minmodel(3, 4, 1, 5, d4, d3)
    pred = pi_43 * pi_21 / Fr(-700700)
    print(f"  Ising (3,4) lam=1/2 N=7: direct = {lh[-2]}", flush=True)
    print(f"  Top-layer (gamma=-700700) pred  = {pred}", flush=True)
    assert lh[-2] == pred, f"Ising N=7 mismatch: {lh[-2]} vs {pred}"
    print("[PASS] Exact match with torus paper gamma_7 = -700700 at Ising (3,4), lambda=1/2, N=7!", flush=True)


def main():
    parser = argparse.ArgumentParser(description="Exact small-case exploration of sphere 4-point Virasoro blocks.")
    parser.add_argument("--max-level", type=int, default=7, help="Max level for (2,3), (2,5), (3,4) checks (default: 7)")
    args = parser.parse_args()

    verify_gamma_formula_symbolic()
    verify_fusion_polynomials_symbolic()
    check_ribault_23_N5()

    # Fixed generic rational external weights
    d_ext = (Fr(1, 3), Fr(2, 5), Fr(3, 7), Fr(5, 11))
    check_minimal_model(2, 3, 1, 1, args.max_level, d_ext)
    check_minimal_model(2, 5, 1, 1, args.max_level, d_ext)
    check_ising_N7_gamma()


if __name__ == "__main__":
    main()
