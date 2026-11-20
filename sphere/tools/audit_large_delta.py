#!/usr/bin/env python3
"""Exact symbolic and rational audit of all lemmas in S1_ASYMP (sphere/notes/s1_asymptotics.md)."""

from __future__ import annotations

import argparse
from fractions import Fraction as Fr
import sympy as sp


def compute_B_matrix_exact(N: int) -> list[list[Fr]]:
    """Compute exact B_{m,n} (1 <= m, n <= N) from B(p,q) = -pq / (2 s1 s2 (s1+s2)^2) in O(N^3) exact Fraction ops."""
    from sphere.tools.exact_sphere_block import series_mul, series_inv
    # s(p) = sqrt(1 - p) = sum_{k>=0} binom(1/2, k) (-p)^k
    s_p = [Fr(1)]
    for k in range(1, N + 1):
        s_p.append(s_p[-1] * Fr(2 * k - 3, 2 * k))
        # Wait: binom(1/2, k) (-1)^k = -(1/2) * (1/2) * (3/2) ... / k!
    # Double-check s_p: k=0 -> 1, k=1 -> -1/2, k=2 -> -1/8, k=3 -> -1/16!
    s_p = [Fr(1)]
    for k in range(1, N + 1):
        s_p.append(s_p[-1] * Fr(2 * k - 3, 2 * k))
    # Wait: k=1: 1 * (-1)/2 = -1/2; k=2: (-1/2) * (1)/4 = -1/8; k=3: (-1/8) * (3)/6 = -1/16! EXACT!
    inv_s = series_inv(s_p, N)
    # p / s(p) = [0] + inv_s[:N]
    ps = [Fr(0)] + inv_s[:N]
    # Note 1/(s1 + s2)^2 = 1/(2 - (1-s1) - (1-s2))^2 = (1/4) sum_{k>=0} (k+1) ((1-s1)/2 + (1-s2)/2)^k!
    # Let u(p) = (1 - s(p))/2 (starts at p^1 with 1/4 p + ...).
    u_p = [Fr(0)] + [-s_p[k] / 2 for k in range(1, N + 1)]
    # Precompute powers u(p)^a for a = 0..N
    u_pows = [[Fr(1)] + [Fr(0)] * N]
    for a in range(1, N + 1):
        u_pows.append(series_mul(u_pows[-1], u_p, N))
    # Compute C_{i,j} = [p^i q^j] 1/(s1 + s2)^2 = (1/4) sum_{a+b<=i+j} (a+b+1) binom(a+b, a) u_pows[a][i] u_pows[b][j]
    # Even faster: for each a, b with a <= N, b <= N, add (a+b+1)*binom(a+b, a)/4 * outer(u_pows[a], u_pows[b])
    # Wait: multiply by ps(p) and ps(q) first: ps_u[a] = ps(p) * u(p)^a!
    ps_u = [series_mul(ps, u_pows[a], N) for a in range(N + 1)]
    from math import comb
    B = [[Fr(0)] * N for _ in range(N)]
    for a in range(N):
        pa = ps_u[a]
        for b in range(N):
            pb = ps_u[b]
            w = Fr(-(a + b + 1) * comb(a + b, a), 8)  # -1/2 * 1/4 = -1/8
            for m in range(1, N + 1):
                if pa[m]:
                    wm = w * pa[m]
                    row = B[m - 1]
                    for n in range(1, N + 1):
                        if pb[n]:
                            row[n - 1] += wm * pb[n]
    return B


def audit_lemma_a3(max_z: int = 7) -> None:
    print("=== Auditing Lemma A3 (S^(0) PDE, half-pillow, Wiener-Hopf saddle point) ===", flush=True)
    s1, s2, s3 = sp.symbols("s1 s2 s3", positive=True)
    p = 1 - s1**2
    q = 1 - s2**2
    r = 1 - s3**2

    A_s = lambda s: -2 * sp.I * (1 / s - 1)
    B_ss = lambda sa, sb: -sp.Rational(1, 2) * (1 - sa**2) * (1 - sb**2) / (sa * sb * (sa + sb)**2)

    # 1. sigma^0 equation: i A(p) - 1/4 A(p)^2 - p/(1-p) = 0
    eq0 = sp.cancel(sp.I * A_s(s1) - sp.Rational(1, 4) * A_s(s1)**2 - p / (1 - p))
    assert eq0 == 0, f"sigma^0 failed: {eq0}"

    # 2. sigma^1 equation: (2i - A(p)) B(p,q) + q d/dq((p A(q) - q A(p))/(q - p) - p/(1-p) A(q)) = 0
    # Note q d/dq = -((1 - s2^2) / (2 s2)) d/ds2
    qd_dq = lambda expr: -((1 - s2**2) / (2 * s2)) * sp.diff(expr, s2)
    eq1 = sp.cancel((2 * sp.I - A_s(s1)) * B_ss(s1, s2) + qd_dq((p * A_s(s2) - q * A_s(s1)) / (q - p) - (p / (1 - p)) * A_s(s2)))
    assert eq1 == 0, f"sigma^1 failed: {eq1}"

    # 3. sigma^2 equation:
    # m(B_{l, m+k} - B_{l, m}) + l(B_{m, l+k} - B_{m, l}) - sum_{n=1}^{k-1} B_{m, n} B_{l, k-n} = 0
    rd_dr = lambda expr: -((1 - s3**2) / (2 * s3)) * sp.diff(expr, s3)
    term_q = qd_dq((p * B_ss(s2, s3) - q * B_ss(s1, s3)) / (q - p) - (p / (1 - p)) * B_ss(s2, s3))
    term_r = rd_dr((p * B_ss(s2, s3) - r * B_ss(s1, s2)) / (r - p) - (p / (1 - p)) * B_ss(s2, s3))
    eq2 = sp.cancel(term_q + term_r - B_ss(s1, s2) * B_ss(s1, s3))
    assert eq2 == 0, f"sigma^2 failed: {eq2}"

    # 4. Second-derivative trace: -1/2 B(p, p) = p^2 / (16 (1-p)^2)
    eq_tr = sp.cancel(-sp.Rational(1, 2) * B_ss(s1, s1) - p**2 / (16 * (1 - p)**2))
    assert eq_tr == 0, f"B(p,p) trace failed: {eq_tr}"

    # 5. Half-pillow Jacobian identities
    w, v = sp.symbols("w v")
    sw = (1 - w) / (1 + w)
    sv = (1 - v) / (1 + v)
    assert sp.cancel(sw * A_s(sw) - (-4 * sp.I * w / (1 + w))) == 0
    assert sp.cancel(sw * sv * B_ss(sw, sv) - (-2 * w * v / (1 - w * v)**2)) == 0

    # 6. Wiener-Hopf saddle point, I_0(z) = log(16q/z), and 1 - g_*(+-1) through z^{max_z}
    z = sp.symbols("z")
    I0 = sum(sp.binomial(-sp.Rational(1, 2), n)**2 * z**n for n in range(max_z + 1))
    # a_m(z) = [x^m] Omega(x; z) = (1/I0) sum_{k>=0} binom(-1/2, m+k) binom(-1/2, k) (-1)^m z^k
    a = {}
    for m in range(1, max_z + 1):
        num = sum(
            sp.binomial(-sp.Rational(1, 2), m + k) * sp.binomial(-sp.Rational(1, 2), k) * ((-1) ** (m + 2 * k)) * z**k
            for k in range(max_z + 1)
        )
        a[m] = sp.series(num / I0, z, 0, max_z + 1).removeO()

    # Verify (I + M(z)) sigma_* = -(1/2) D^{-1} Z A mod z^{max_z+1}
    pp = sp.symbols("pp")
    A_ser = sp.series(-2 * sp.I * ((1 - pp)**(-sp.Rational(1, 2)) - 1), pp, 0, max_z + 1).removeO()
    A_vec = [sp.expand(A_ser.coeff(pp, m)) for m in range(1, max_z + 1)]
    B_fr = compute_B_matrix_exact(max_z)
    B_mat = [[sp.Rational(B_fr[i][j].numerator, B_fr[i][j].denominator) for j in range(max_z)] for i in range(max_z)]

    sig_star = [sp.series(sp.I * a[m] * z**m / m, z, 0, max_z + 1).removeO() for m in range(1, max_z + 1)]
    for m in range(1, max_z + 1):
        lhs = sig_star[m - 1] + sum(z**m * B_mat[m - 1][n - 1] * sig_star[n - 1] / m for n in range(1, max_z + 1))
        rhs = -z**m * A_vec[m - 1] / (2 * m)
        diff = sp.series(lhs - rhs, z, 0, max_z + 1).removeO()
        assert diff == 0, f"Saddle eq failed at m={m}: {diff}"

    # Verify z d/dz I_0(z) = 2 sum a_m^2 z^m = 1/((1-z) I0^2) - 1 = z d/dz log(16q/z)
    from sphere.tools.exact_sphere_block import theta_series, series_mul
    th3_f, th4_f, z16_f, _ = theta_series(max_z + 1)
    # z(q) = sum_{k>=1} z_c[k] q^k where z_c[k] = 16 * z16_f[k-1]
    z_c = [Fr(0)] + [Fr(16) * z16_f[k - 1] for k in range(1, max_z + 2)]
    # Exact series reversion q(z) = sum_{k>=1} q_c[k] z^k mod z^{max_z+2}
    q_c = [Fr(0)] * (max_z + 2)
    q_c[1] = Fr(1, 16)
    for n in range(2, max_z + 2):
        # Compute [z^n] z(q_trunc(z)) using q_c[1..n-1]
        # Powers of q_trunc mod z^{n+1}
        qpow = [Fr(0)] * (n + 1)
        qpow[0] = Fr(1)
        val_n = Fr(0)
        for k in range(1, n + 1):
            qpow = series_mul(qpow, q_c[: n + 1], n)
            if z_c[k]:
                val_n += z_c[k] * qpow[n]
        q_c[n] = -val_n / Fr(16)

    q_of_z = sum(sp.Rational(q_c[k].numerator, q_c[k].denominator) * z**k for k in range(1, max_z + 2))
    q_sym = sp.symbols("q_sym")
    th3_q = 1 + 2 * q_sym + 2 * q_sym**4 + 2 * q_sym**9
    th4_q = 1 - 2 * q_sym + 2 * q_sym**4 - 2 * q_sym**9

    dI0_saddle = sp.series(2 * sum(a[m]**2 * z**m for m in range(1, max_z + 1)), z, 0, max_z + 1).removeO()
    dI0_jacobi = sp.series(z * sp.diff(sp.log(16 * q_of_z / z), z), z, 0, max_z + 1).removeO()
    assert sp.expand(dI0_saddle - dI0_jacobi) == 0, f"I_0 derivative mismatch: {dI0_saddle - dI0_jacobi}"

    # Verify 1 - g_*(1) = th4(q)^{-2} and 1 - g_*(-1) = th3(q)^{-2}
    # C_+(p) = (i/2) p (1-p)^{-3/2}, C_-(p) = -(i/2) p (1-p)^{-1/2}
    Cp_ser = sp.series(sp.I / 2 * pp * (1 - pp)**(-sp.Rational(3, 2)), pp, 0, max_z + 1).removeO()
    Cm_ser = sp.series(-sp.I / 2 * pp * (1 - pp)**(-sp.Rational(1, 2)), pp, 0, max_z + 1).removeO()
    g1_star = sp.series(sum(Cp_ser.coeff(pp, m) * sig_star[m - 1] for m in range(1, max_z + 1)), z, 0, max_z + 1).removeO()
    gm1_star = sp.series(sum(Cm_ser.coeff(pp, m) * sig_star[m - 1] for m in range(1, max_z + 1)), z, 0, max_z + 1).removeO()
    th3_z = sp.series(th3_q.subs(q_sym, q_of_z), z, 0, max_z + 1).removeO()
    th4_z = sp.series(th4_q.subs(q_sym, q_of_z), z, 0, max_z + 1).removeO()
    assert sp.series((1 - g1_star) - th4_z**(-2), z, 0, max_z + 1).removeO() == 0
    assert sp.series((1 - gm1_star) - th3_z**(-2), z, 0, max_z + 1).removeO() == 0
    print(f"[PASS] Lemma A3 verified symbolically and through z^{max_z}", flush=True)


def audit_lemma_a4(max_z: int = 8) -> None:
    print("=== Auditing Lemma A4 (Bergman kernel & det(I - M^2)^{-1/2}) ===", flush=True)
    s1, s2 = sp.symbols("s1 s2", positive=True)
    p = 1 - s1**2
    q = 1 - s2**2
    B_ss = -sp.Rational(1, 2) * p * q / (s1 * s2 * (s1 + s2)**2)

    # 1. Rational twist identity
    lhs = sp.simplify(s1 * (B_ss - p * q / (p - q)**2))
    rhs = sp.simplify(-p * q * (2 - p - q) / (2 * s2 * (p - q)**2))
    assert sp.simplify(lhs - rhs) == 0, f"Rational twist identity failed: {lhs - rhs}"

    # 2. Coincidence limit W_no(x, x) and residues at x = 0, z
    z, x, eps = sp.symbols("z x eps")
    P = x * (x - z) * (x - 1)
    x1, x2 = sp.symbols("x1 x2")
    S = sp.Rational(1, 2) * (x1 * x2 * (x1 + x2) - 2 * (1 + z) * x1 * x2 + z * (x1 + x2))
    Pp, Ppp = sp.diff(P, x), sp.diff(P, x, 2)
    a1, a2 = Pp / P, Ppp / (2 * P)
    inv_sqrt = 1 - sp.Rational(1, 2) * a1 * eps + (sp.Rational(3, 8) * a1**2 - sp.Rational(1, 2) * a2) * eps**2
    prod_ser = sp.series(sp.expand(S.subs({x1: x, x2: x + eps})) / P * inv_sqrt, eps, 0, 3).removeO()
    W0_no = sp.simplify(sp.diff(prod_ser, eps, 2).subs(eps, 0) / 2)
    assert sp.simplify(W0_no - (x**2 - z)**2 / (8 * x**2 * (x - 1)**2 * (x - z)**2)) == 0
    res0 = sp.simplify(sp.residue(x * W0_no / 2, x, 0) + sp.residue(x * W0_no / 2, x, z))
    assert sp.simplify(res0 - z / (8 * (z - 1))) == 0
    resC = sp.simplify(sp.residue(x / (2 * P), x, 0) + sp.residue(x / (2 * P), x, z))
    assert sp.simplify(resC - 1 / (2 * (z - 1))) == 0

    # 3. Direct determinant check det(I - M^2)^{-1/2} = (1-z)^{-1/8} 2F1(1/2,1/2;1;z)^{-1/2} through z^{max_z}
    B_mat = compute_B_matrix_exact(max_z)

    # Compute log det(I - M(z)^2)^{-1/2} = (1/2) sum_{k>=1} Tr(M(z)^{2k}) / k mod z^{max_z+1}
    # M(z)_{m,n} = z^m B_{m,n} / m, so M(z)^2 has entries of z-degree >= 2!
    # Work with truncated polynomial matrices in z mod z^{max_z+1}
    def mat_mul_trunc(A, B):
        C = [[[Fr(0)] * (max_z + 1) for _ in range(max_z)] for _ in range(max_z)]
        for i in range(max_z):
            for k in range(max_z):
                aik = A[i][k]
                if not any(aik):
                    continue
                for j in range(max_z):
                    bkj = B[k][j]
                    if not any(bkj):
                        continue
                    cij = C[i][j]
                    for d1, v1 in enumerate(aik):
                        if not v1:
                            continue
                        for d2 in range(max_z + 1 - d1):
                            v2 = bkj[d2]
                            if v2:
                                cij[d1 + d2] += v1 * v2
        return C

    M = [[[Fr(0)] * (max_z + 1) for _ in range(max_z)] for _ in range(max_z)]
    for i in range(max_z):
        for j in range(max_z):
            M[i][j][i + 1] = B_mat[i][j] / (i + 1)
    M2 = mat_mul_trunc(M, M)
    log_det = [Fr(0)] * (max_z + 1)
    cur = M2
    for k in range(1, max_z // 2 + 1):
        for i in range(max_z):
            for d in range(max_z + 1):
                log_det[d] += cur[i][i][d] / (2 * k)
        if k < max_z // 2:
            cur = mat_mul_trunc(cur, M2)

    # Exact Fraction logarithm of (1-z)^{-1/8} * I0(z)^{-1/2} mod z^{max_z+1}
    # Using exact recurrence: (log f)' = f' / f!
    I0_f = [Fr(1)]
    for n in range(1, max_z + 1):
        # binom(-1/2, n)^2 = ( (2n-1)/(2n) )^2 * prev
        I0_f.append(I0_f[-1] * Fr(2 * n - 1, 2 * n)**2)
    # log(I0) = sum_{d>=1} L[d] z^d, where d*L[d] = d*I0[d] - sum_{j=1}^{d-1} j*L[j]*I0[d-j]
    log_I0 = [Fr(0)] * (max_z + 1)
    for d in range(1, max_z + 1):
        s = Fr(d) * I0_f[d]
        for j in range(1, d):
            s -= Fr(j) * log_I0[j] * I0_f[d - j]
        log_I0[d] = s / Fr(d)
    for d in range(1, max_z + 1):
        td = Fr(1, 8 * d) - Fr(1, 2) * log_I0[d]
        assert log_det[d] == td, f"det mismatch at z^{d}: {log_det[d]} vs {td}"
    print(f"[PASS] Lemma A4 verified symbolically and through z^{max_z}", flush=True)


def audit_lemma_a5() -> None:
    print("=== Auditing Lemma A5 (L_k^(0) log(1 - g(+-1)) in rational (s1, s2)) ===", flush=True)
    s1, s2 = sp.symbols("s1 s2", positive=True)
    p = 1 - s1**2
    q = 1 - s2**2
    A_s = -2 * sp.I * (1 / s1 - 1)
    B_ss = -sp.Rational(1, 2) * p * q / (s1 * s2 * (s1 + s2)**2)
    qd_dq = lambda expr: -((1 - s2**2) / (2 * s2)) * sp.diff(expr, s2)

    for name, C_fn, expected_const in [
        ("g(1)", lambda s: sp.I / 2 * (1 - s**2) / s**3, -p / (2 * (1 - p)**2)),
        ("g(-1)", lambda s: -sp.I / 2 * (1 - s**2) / s, p / (2 * (1 - p))),
    ]:
        Cp, Cq = C_fn(s1), C_fn(s2)
        c_gf = sp.cancel((sp.I - sp.Rational(1, 2) * A_s) * Cp)
        assert sp.cancel(c_gf - expected_const) == 0, f"{name} const GF failed"
        lin_gf = qd_dq((p * Cq - q * Cp) / (q - p) - (p / (1 - p)) * Cq) - B_ss * Cp
        assert sp.cancel(lin_gf - (-expected_const) * Cq) == 0, f"{name} linear GF failed"
    print("[PASS] Lemma A5 verified identically for all k >= 1", flush=True)


def audit_lemma_a6() -> None:
    print("=== Auditing Lemma A6 (Virasoro diffeomorphism & Jacobi identity) ===", flush=True)
    y, X, q = sp.symbols("y X q")
    phi = 4 * (1 - sp.sqrt(1 - y)) / (1 + sp.sqrt(1 - y))
    assert sp.simplify(sp.diff(sp.log(phi / y), y) - ((1 - y)**(-sp.Rational(1, 2)) - 1) / y) == 0
    x_of_X = X + sp.Rational(1, 2) + 1 / (16 * X)
    assert sp.simplify(x_of_X * (x_of_X - 1) - (X - 1 / (16 * X))**2) == 0
    assert sp.simplify(sp.diff(x_of_X, X) - (X - 1 / (16 * X)) / X) == 0

    # Verify Jacobi identity 16 q prod_{m>=1} (1 - q^{2m})^{12} == z(q) (1 - z(q)) th3(q)^{12} mod q^{13}
    M = 12
    th3 = 1 + 2 * q + 2 * q**4 + 2 * q**9
    th4 = 1 - 2 * q + 2 * q**4 - 2 * q**9
    lhs = 16 * q
    for m in range(1, M // 2 + 1):
        lhs = sp.series(lhs * (1 - q**(2 * m))**12, q, 0, M + 1).removeO()
    rhs = sp.series((th3**4 - th4**4) * th4**4 * th3**4, q, 0, M + 1).removeO()
    assert sp.expand(lhs - rhs) == 0, f"Jacobi identity failed: {lhs - rhs}"
    print("[PASS] Lemma A6 verified identically (and Jacobi product through q^12)", flush=True)


def audit_theorem_s1a(max_level: int = 5) -> None:
    print(f"=== Auditing Theorem S1A (deg_Delta(num H_N) < deg_Delta(det G_N), N=1..{max_level}) ===", flush=True)
    from sphere.tools.exact_sphere_block import reconstruct_B_and_H

    cases = [
        ("c=1/2 (Ising)", Fr(1, 2), (Fr(1, 16), Fr(1, 2), Fr(3, 7), Fr(5, 11))),
        ("c=2", Fr(2), (Fr(1, 8), Fr(1, 8), Fr(2, 5), Fr(7, 9))),
        ("c=25/7", Fr(25, 7), (Fr(1, 3), Fr(2, 5), Fr(3, 7), Fr(4, 9))),
    ]
    for label, c_val, d_ext in cases:
        _, H_funcs = reconstruct_B_and_H(c_val, d_ext, max_level)
        for N in range(1, max_level + 1):
            deg_num = len(H_funcs[N].num) - 1
            deg_den = len(H_funcs[N].den) - 1
            assert deg_num < deg_den, f"{label} N={N}: deg_num={deg_num} >= deg_den={deg_den}"
        print(f"  [PASS] {label}: deg(num H_N) < deg(den H_N) for N=1..{max_level}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit all lemmas and Theorem S1A of S1_ASYMP.")
    parser.add_argument("--max-z", type=int, default=7, help="Series order for A3/A4 checks (default: 7)")
    parser.add_argument("--max-level", type=int, default=5, help="Max Gram-matrix level for Theorem S1A check (default: 5)")
    args = parser.parse_args()

    audit_lemma_a3(args.max_z)
    audit_lemma_a4(args.max_z + 1)
    audit_lemma_a5()
    audit_lemma_a6()
    audit_theorem_s1a(args.max_level)
    print("\nALL S1_ASYMP AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
