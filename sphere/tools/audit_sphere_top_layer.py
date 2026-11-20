#!/usr/bin/env python3
"""Exact rational audit of S2: top Jantzen layer formula and unconditional sharpness for B_N and H_N."""

from __future__ import annotations

import argparse
from fractions import Fraction as Fr
from math import factorial
import sympy as sp

from sphere.tools.exact_sphere_block import (
    make_gram_builder,
    gamma_poly,
    solve_quad_form,
    reconstruct_B_and_H,
    theta_series,
    series_mul,
    series_pow_rational,
    peval,
)
from sphere.tools.audit_sphere_confluence import P_series


def eval_P_rs(r: int, s: int, da: Fr, db: Fr, p: int, pp: int) -> Fr:
    """Evaluate P_{r,s}(b_*, da, db) exactly at b_*^2 = -p'/p."""
    return P_series(r, s, da, db, Fr(-pp, p), 0).coeff(0)


def layer_data(p: int, pp: int, r: int, s: int, k: int):
    """Return (ell_small, ell_big, m_small, m_big, pi_small_fn, pi_big_fn) for layer k >= 1."""
    n1 = pp * r + p * s
    n0 = pp * r - p * s
    assert n1 < p * pp and n0 != 0
    if k % 2 == 1:
        j = (k - 1) // 2
        R_plus, S_plus = r + j * p, s + j * pp
        R_minus, S_minus = (j + 1) * p - r, (j + 1) * pp - s
        ell_p, ell_m = R_plus * S_plus, R_minus * S_minus
        m_p, m_m = 2 * j * p * pp + n1, 2 * (j + 1) * p * pp - n1
        pi_p = lambda da, db: eval_P_rs(R_plus, S_plus, da, db, p, pp)
        pi_m = lambda da, db: eval_P_rs(R_minus, S_minus, da, db, p, pp)
    else:
        j = k // 2
        R_plus, S_plus = r + j * p, j * pp - s
        R_minus, S_minus = j * p - r, j * pp + s
        ell_p, ell_m = j * (j * p * pp + n0), j * (j * p * pp - n0)
        m_p, m_m = 2 * j * p * pp + n0, 2 * j * p * pp - n0
        pi_p = lambda da, db: eval_P_rs(r, s, da, db, p, pp) * eval_P_rs(R_plus, S_plus, da, db, p, pp)
        pi_m = lambda da, db: eval_P_rs(r, s, da, db, p, pp) * eval_P_rs(R_minus, S_minus, da, db, p, pp)

    if m_p < m_m:
        return ell_p, ell_m, m_p, m_m, pi_p, pi_m
    return ell_m, ell_p, m_m, m_p, pi_m, pi_p


def eval_B_at_weight(gm, h_val: Fr, d_ext: tuple[Fr, Fr, Fr, Fr], level: int) -> Fr:
    if level == 0:
        return Fr(1)
    d1, d2, d3, d4 = d_ext
    basis, G = gm(level)
    Gx = [[peval(e, h_val) for e in row] for row in G]
    vL = [peval(gamma_poly(Y, d4, d3), h_val) for Y in basis]
    vR = [peval(gamma_poly(Y, d1, d2), h_val) for Y in basis]
    det, val = solve_quad_form(Gx, vL, vR)
    assert det != 0, f"Gram matrix singular at h={h_val}, level={level}"
    return val


def eval_H_at_weight(gm, c_val: Fr, h_val: Fr, d_ext: tuple[Fr, Fr, Fr, Fr], max_M: int) -> list[Fr]:
    d1, d2, d3, d4 = d_ext
    B = [eval_B_at_weight(gm, h_val, d_ext, m) for m in range(max_M + 1)]
    th3, _, z16, omz = theta_series(max_M)
    psi1 = series_pow_rational(z16, h_val - (c_val - 1) / 24, max_M)
    psi2 = series_pow_rational(omz, d2 + d3 - (c_val - 1) / 24, max_M)
    psi3 = series_pow_rational(th3, 4 * (d1 + d2 + d3 + d4) - (c_val - 1) / 2, max_M)
    pref = series_mul(series_mul(psi1, psi2, max_M), psi3, max_M)
    z16_pows = [[Fr(1)] + [Fr(0)] * max_M]
    for m in range(1, max_M + 1):
        z16_pows.append(series_mul(z16_pows[-1], z16, max_M))
    Bz = [Fr(0)] * (max_M + 1)
    for m in range(max_M + 1):
        fac16 = Fr(16**m)
        for k in range(max_M + 1 - m):
            Bz[m + k] += B[m] * fac16 * z16_pows[m][k]
    Hq = series_mul(pref, Bz, max_M)
    return [Hq[m] / Fr(16**m) for m in range(max_M + 1)]


def audit_top_layer_and_gamma(max_level: int = 7) -> None:
    print(f"=== Auditing Theorem S2B (top-layer formula for B_N and H_N, N <= {max_level}) ===", flush=True)
    # Test multiple minimal models including Ising (3,4) lam=1/2 (gamma_7 = -700700),
    # (2,3) lam=0 (k=1: ell=1,2; k=2: ell=5,7), (2,5) lam=0 (k=1: ell=1,4; k=2: ell=6) and lam=-1/5 (k=1: ell=2,3)
    d_ext = (Fr(1, 5), Fr(2, 7), Fr(3, 11), Fr(4, 13))
    cases = [
        (2, 3, 1, 1, None),       # lam = 0: k=1 (1,2), k=2 (5,7)
        (2, 5, 1, 1, None),       # lam = 0: k=1 (1,4), k=2 (6,14)
        (2, 5, 1, 2, None),       # lam = -1/5: k=1 (2,3), k=2 (9,11)
        (3, 4, 1, 1, None),       # Ising lam = 0: k=1 (1,6)
        (3, 4, 2, 1, {2: (-700700, None)}),  # Ising lam = 1/2: k=1 (2,3), k=2 (7,17), gamma_7 = -700700!
    ]
    for p, pp, r, s, known_gammas in cases:
        c_val = Fr(1) - Fr(6 * (pp - p)**2, p * pp)
        lam = Fr((pp * r - p * s)**2 - (pp - p)**2, 4 * p * pp)
        B_funcs, H_funcs = reconstruct_B_and_H(c_val, d_ext, max_level)
        gm = make_gram_builder(c_val)

        # Compute layer cutoffs up to max_level
        layers = []
        for k in range(1, 10):
            ell_s, ell_b, m_s, m_b, pi_s, pi_b = layer_data(p, pp, r, s, k)
            if ell_s > max_level:
                break
            layers.append((k, ell_s, ell_b, m_s, m_b, pi_s, pi_b))

        for idx, (k, ell_s, ell_b, m_s, m_b, pi_s, pi_b) in enumerate(layers):
            next_ell = layers[idx + 1][1] if idx + 1 < len(layers) else max_level + 1
            mu_s = lam + ell_s
            mu_b = lam + ell_b
            # Extract gamma_small from N = ell_s (single vector, M = 0, B_0 = H_0 = 1)
            ord_B0, lB0 = B_funcs[ell_s].laurent_at(lam, 0)
            ord_H0, lH0 = H_funcs[ell_s].laurent_at(lam, 0)
            assert ord_B0 == k and ord_H0 == k
            num_s = pi_s(d_ext[3], d_ext[2]) * pi_s(d_ext[0], d_ext[1])
            gamma_s = num_s / lB0[-k]
            assert gamma_s == num_s / lH0[-k], "gamma_s mismatch between B and H!"
            if known_gammas and k in known_gammas and known_gammas[k][0] is not None:
                assert gamma_s == Fr(known_gammas[k][0]), f"Expected gamma={known_gammas[k][0]}, got {gamma_s}"

            gamma_b = None
            if ell_b <= max_level and ell_b < next_ell:
                # Extract gamma_big from N = ell_b!
                M_at_b = ell_b - ell_s
                B_sub = eval_B_at_weight(gm, mu_s, d_ext, M_at_b)
                ord_Bb, lBb = B_funcs[ell_b].laurent_at(lam, 0)
                assert ord_Bb == k
                num_b = pi_b(d_ext[3], d_ext[2]) * pi_b(d_ext[0], d_ext[1])
                rem_b = lBb[-k] - (num_s / gamma_s) * B_sub
                gamma_b = num_b / rem_b

            # Now verify EVERY N in [ell_s, min(max_level, next_ell - 1)] for BOTH B_N and H_N!
            max_M_s = min(max_level, next_ell - 1) - ell_s
            H_s_list = eval_H_at_weight(gm, c_val, mu_s, d_ext, max_M_s)
            H_b_list = None
            if gamma_b is not None:
                max_M_b = min(max_level, next_ell - 1) - ell_b
                H_b_list = eval_H_at_weight(gm, c_val, mu_b, d_ext, max_M_b)

            for N in range(ell_s, min(max_level, next_ell - 1) + 1):
                ord_B, lB = B_funcs[N].laurent_at(lam, 0)
                ord_H, lH = H_funcs[N].laurent_at(lam, 0)
                assert ord_B == k and ord_H == k, f"({p},{pp}) ({r},{s}) N={N}: ord_B={ord_B}, ord_H={ord_H}, k={k}"
                pred_B = (num_s / gamma_s) * eval_B_at_weight(gm, mu_s, d_ext, N - ell_s)
                pred_H = (num_s / gamma_s) * H_s_list[N - ell_s]
                if N >= ell_b:
                    num_b = pi_b(d_ext[3], d_ext[2]) * pi_b(d_ext[0], d_ext[1])
                    pred_B += (num_b / gamma_b) * eval_B_at_weight(gm, mu_b, d_ext, N - ell_b)
                    pred_H += (num_b / gamma_b) * H_b_list[N - ell_b]
                assert lB[-k] == pred_B, f"B top-layer mismatch at ({p},{pp}) ({r},{s}) N={N}"
                assert lH[-k] == pred_H, f"H top-layer mismatch at ({p},{pp}) ({r},{s}) N={N}"

        print(f"  [PASS] ({p},{pp}) (r,s)=({r},{s}) lam={lam}: exact B_N & H_N top-layer match through N={max_level}", flush=True)


def audit_sharpness_specializations() -> None:
    print("=== Auditing Theorem S2C (BPZ (2,1) B_N sharpness) & Theorem S2D (Hermite H_N sharpness) ===", flush=True)
    # Test multiple minimal models, interior weights, layers k=1,2, and M up to 4.
    test_tuples = [
        (2, 3, 1, 1, 1, 3),  # k=1: ell=1,2; next=5 -> max M = 3
        (2, 3, 1, 1, 2, 4),  # k=2: ell=5,7; next=12 -> M up to 4
        (2, 5, 1, 1, 1, 4),  # k=1: ell=1,4; next=6 -> max M = 4
        (2, 5, 1, 2, 1, 4),  # k=1: ell=2,3; next=9 -> M up to 4
        (3, 4, 2, 1, 1, 4),  # Ising lam=1/2 k=1: ell=2,3; next=7 -> max M = 4
        (3, 4, 2, 1, 2, 3),  # Ising lam=1/2 k=2: ell=7,17 -> M up to 3
        (3, 5, 1, 1, 1, 4),  # (3,5) lam=0 k=1: ell=1,8 -> M up to 4
        (3, 5, 1, 2, 2, 3),  # (3,5) k=2 -> M up to 3
    ]
    for p, pp, r, s, k, max_M in test_tuples:
        c_val = Fr(1) - Fr(6 * (pp - p)**2, p * pp)
        lam = Fr((pp * r - p * s)**2 - (pp - p)**2, 4 * p * pp)
        ell_s, ell_b, m_s, m_b, pi_s, pi_b = layer_data(p, pp, r, s, k)
        mu_s = lam + ell_s
        gm = make_gram_builder(c_val)

        # --- Theorem S2C: BPZ (2, 1) specialization ---
        def delta_from_a(a_val: Fr) -> Fr:
            return (a_val * a_val - Fr((pp - p)**2)) / Fr(4 * p * pp)

        a2 = Fr(2 * pp - p)
        a1 = Fr(m_s + pp)
        a3 = Fr(k * p * pp - p)
        a4 = Fr(m_s - m_b + 2 * pp, 2)
        d_bpz = (delta_from_a(a1), delta_from_a(a2), delta_from_a(a3), delta_from_a(a4))

        assert pi_b(d_bpz[3], d_bpz[2]) == 0, f"S2C: pi_big did not vanish for ({p},{pp}) ({r},{s}) k={k}"
        assert pi_s(d_bpz[3], d_bpz[2]) != 0, f"S2C: pi_small(4,3) vanished!"
        assert pi_s(d_bpz[0], d_bpz[1]) != 0, f"S2C: pi_small(1,2) vanished!"

        kappa = Fr((k * p - 1) * pp, 2 * p)
        assert kappa.denominator != 1, f"S2C: kappa={kappa} is integer!"
        for M in range(0, max_M + 1):
            B_M = eval_B_at_weight(gm, mu_s, d_bpz, M)
            binom_k_M = Fr(1)
            for j in range(M):
                binom_k_M *= (kappa - j) / Fr(j + 1)
            expected = ((-1)**M) * binom_k_M
            assert B_M == expected and B_M != 0, f"S2C mismatch at ({p},{pp}) ({r},{s}) k={k} M={M}: {B_M} != {expected}"

        # --- Theorem S2D: Identity-insertion + Hermite specialization ---
        # d1 = mu_s, d2 = 0, Lambda_3 - Lambda_4 = i alpha, Lambda_3 + Lambda_4 = i v (v free!)
        # Note Delta_3 = Q^2/4 + (v + alpha)^2/16, Delta_4 = Q^2/4 + (v - alpha)^2/16
        # Wait: alpha = X / sqrt(p p') where X = m_b - p' - p!
        # Put v = w / sqrt(p p') so (v +/- alpha)^2 = (w +/- X)^2 / (p p') is RATIONAL for rational w!
        X = m_b - pp - p
        assert pi_s(mu_s, Fr(0)) != 0, "S2D: pi_small(mu, 0) vanished!"
        Q2_4 = Fr(-(pp - p)**2, 4 * p * pp)
        # Check pi_big(d4, d3) == 0 and B_m == delta_{m,0} for m <= max_M at several rational w!
        w_vals = [Fr(j) for j in range(1, max_M + 3)]
        H_samples = []
        for w in w_vals:
            d3 = Q2_4 + Fr((w + X)**2, 16 * p * pp)
            d4 = Q2_4 + Fr((w - X)**2, 16 * p * pp)
            assert pi_b(d4, d3) == 0, "S2D: pi_big(d4, d3) != 0!"
            for m in range(1, max_M + 1):
                assert eval_B_at_weight(gm, mu_s, (mu_s, Fr(0), d3, d4), m) == 0
            H_samples.append((w, eval_H_at_weight(gm, c_val, mu_s, (mu_s, Fr(0), d3, d4), max_M)))

        # Interpolate H_M as a polynomial in w and check leading coeff [w^M] == [v^M] / (p*pp)^{M/2}!
        # Specifically: [v^M] H_M = (-1)^M / (16^M M!) H_M(alpha), so
        # [w^M] H_M(w) = (p*pp)^{-M/2} * (-1)^M / (16^M M!) * H_M(X / sqrt(p*pp)) (which is RATIONAL!)
        alpha_sym = X / sp.sqrt(p * pp)
        for M in range(1, max_M + 1):
            # Extract [w^M] via finite difference / Lagrange interpolation of degree M
            pts = [(w_vals[i], H_samples[i][1][M]) for i in range(M + 1)]
            # Leading coeff of interpolating polynomial of degree <= M through (x_i, y_i):
            lead = Fr(0)
            for i, (xi, yi) in enumerate(pts):
                denom = Fr(1)
                for j, (xj, _) in enumerate(pts):
                    if i != j:
                        denom *= (xi - xj)
                lead += yi / denom
            hm_exact = sp.simplify(sp.hermite(M, alpha_sym) / (sp.sqrt(p * pp)**M))
            hm_rat = sp.Rational(hm_exact)
            expected_lead = Fr((-1)**M, (16**M) * factorial(M)) * Fr(hm_rat.p, hm_rat.q)
            assert lead == expected_lead and lead != 0, (
                f"S2D mismatch at ({p},{pp}) ({r},{s}) k={k} M={M}: {lead} != {expected_lead}"
            )

        print(f"  [PASS] ({p},{pp}) (r,s)=({r},{s}) k={k}, M=0..{max_M}: S2C BPZ & S2D Hermite exact match", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit S2 top-layer formula and unconditional sharpness.")
    parser.add_argument("--max-level", type=int, default=7, help="Max level for top-layer Gram audit (default: 7)")
    args = parser.parse_args()

    audit_top_layer_and_gamma(args.max_level)
    audit_sharpness_specializations()
    print("\nALL S2 AUDITS PASSED.", flush=True)


if __name__ == "__main__":
    main()
