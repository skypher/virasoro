#!/usr/bin/env python3
"""Exact check of the Lee--Yang level-four example in Section 6.2 of paper.tex.

Lee--Yang charge (p,p') = (2,5), c = -22/5, interior weight lambda = h_{1,2} = -1/5.
The first Jantzen layer has singular vectors at levels 2 and 3, the second layer
starts at level 9, so N = 4 is the lowest level on which both first-layer vectors
contribute to the top coefficient (Theorem 5.9, eq. (5.1)).

The script computes H_N(c, Delta, d) for N <= 4 by inverting the Shapovalov
matrix (tools/exact_shapovalov.py), reads off the Jantzen norms from levels 2
and 3, checks the top-layer formula at level 4, compares the Jantzen norms with
Proposition 6.7, and prints the two summands of the top coefficient at
d_1 = h_{1,3}(b_star) = -1/5 with their 5-adic valuations (Case 2 of the proof of
Proposition 6.9).  Every check prints PASS or FAIL; the exit code is the number
of failures.

Usage: python3 -u tools/check_leeyang_level4_example.py
"""

import sys
import time

import sympy as sp

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import exact_shapovalov as es  # noqa: E402

h, d = es.h, es.d
C = sp.Rational(-22, 5)
LAM = sp.Rational(-1, 5)
FAIL = 0
T0 = time.time()


def log(msg):
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


def check(name, ok):
    global FAIL
    log(f"{'PASS' if ok else 'FAIL'}: {name}")
    if not ok:
        FAIL += 1


def v5(x):
    x = sp.Rational(x)
    if x == 0:
        return None
    n, m = x.p, x.q
    v = 0
    while n % 5 == 0:
        n //= 5
        v += 1
    while m % 5 == 0:
        m //= 5
        v -= 1
    return v


def dx(x):
    # d_x = (x^2 - (p'-p)^2)/(4pp') with (p,p') = (2,5)
    return sp.Rational(x * x - 9, 40)


def torus_norm(R, S):
    # N_{R,S}(b_star, d) = prod over odd a < 2R, odd l < 2S of (d - d_{p'a-pl})(d - d_{p'a+pl})
    out = sp.Integer(1)
    for a in range(1, 2 * R, 2):
        for l in range(1, 2 * S, 2):
            out *= (d - dx(5 * a - 2 * l)) * (d - dx(5 * a + 2 * l))
    return sp.expand(out)


def main():
    log("computing H_N(c=-22/5, Delta, d) for N <= 4 by Shapovalov inversion")
    _, H = es.h_coefficients(4, C)
    top = {}
    for N in range(1, 5):
        expr = sp.cancel(H[N])
        order = es.pole_order(expr, LAM)
        log(f"N={N}: pole order at Delta=-1/5 is {order}")
        check(f"N={N} pole order is {1 if N >= 2 else 0}", order == (1 if N >= 2 else 0))
        top[N] = sp.factor(sp.cancel(sp.limit((h - LAM) * expr, h, LAM))) if order else 0

    Np = torus_norm(1, 2)  # N^+_1, level 2
    Nm = torus_norm(1, 3)  # N^-_1, level 3
    log(f"N^+_1 = {sp.factor(Np)}")
    log(f"N^-_1 = {sp.factor(Nm)}")

    ratio_p = sp.cancel(top[2] / Np)
    check("top_2 is a constant multiple of N^+_1", ratio_p.free_symbols == set())
    gamma_p = 1 / ratio_p
    H1_mup = sp.cancel(H[1].subs(h, LAM + 2))
    H2_mup = sp.cancel(H[2].subs(h, LAM + 2))
    H1_mum = sp.cancel(H[1].subs(h, LAM + 3))
    rest3 = sp.cancel(top[3] - Np / gamma_p * H1_mup)
    ratio_m = sp.cancel(rest3 / Nm)
    check("top_3 - (N^+/gamma^+) H_1(9/5) is a constant multiple of N^-_1",
          ratio_m.free_symbols == set())
    gamma_m = 1 / ratio_m
    log(f"gamma^+_1 = {gamma_p}, gamma^-_1 = {gamma_m}")

    lin_p = sp.Poly(sp.expand(Np / gamma_p), d).coeff_monomial(d)
    lin_m = sp.Poly(sp.expand(Nm / gamma_m), d).coeff_monomial(d)
    log(f"[d](N^+/gamma^+) = {lin_p}, [d](N^-/gamma^-) = {lin_m}")
    check("Prop 6.7: [d](N^pm/gamma^pm) = pm rho with |rho| = n_0/(2(p'-p)) = 1/6 (k = 1, c_1 = 1)",
          abs(lin_p) == sp.Rational(1, 6) and lin_m == -lin_p)

    term_p = sp.expand(Np / gamma_p * H2_mup)
    term_m = sp.expand(Nm / gamma_m * H1_mum)
    check("Theorem 5.9 at N=4: top_4 = (N^+/gamma^+) H_2(9/5,d) + (N^-/gamma^-) H_1(14/5,d)",
          sp.cancel(top[4] - term_p - term_m) == 0)
    log(f"H_1(c, 14/5, d) = {sp.factor(H1_mum)}")
    log(f"H_2(c, 9/5, d) = {sp.factor(H2_mup)}")
    log(f"top_4(d) = {sp.factor(top[4])}")

    d1 = sp.Rational(-1, 5)
    a_p = sp.cancel(term_p / (d - d1)).subs(d, d1)
    a_m = sp.cancel(term_m / (d - d1)).subs(d, d1)
    check("both summands vanish at d_1 = -1/5", term_p.subs(d, d1) == 0 and term_m.subs(d, d1) == 0)
    log(f"[(d-d_1)] summand +: {a_p}  (v_5 = {v5(a_p)})")
    log(f"[(d-d_1)] summand -: {a_m}  (v_5 = {v5(a_m)})")
    check("5-adic valuations of the two summands at d_1 differ by -1 (Case 2: -(v(2!)-v(1!))-(2-1)a)",
          v5(a_p) - v5(a_m) == -1)
    check("their sum is nonzero", a_p + a_m != 0)
    log(f"[(d-d_1)] top_4 = {a_p + a_m}")
    vals = {
        "H_2(9/5, d_1)": H2_mup.subs(d, d1),
        "H_1(14/5, d_1)": H1_mum.subs(d, d1),
        "[(d-d_1)] N^+_1": sp.cancel(Np / (d - d1)).subs(d, d1),
        "[(d-d_1)] N^-_1": sp.cancel(Nm / (d - d1)).subs(d, d1),
    }
    for k, v in vals.items():
        log(f"{k} = {v}  (v_5 = {v5(v)})")
    check("eq (6.x) valuation of H_2(9/5, d_1) is -2", v5(vals["H_2(9/5, d_1)"]) == -2)
    check("eq (6.x) valuation of H_1(14/5, d_1) is -1", v5(vals["H_1(14/5, d_1)"]) == -1)
    log(f"done, {FAIL} failure(s)")
    return FAIL


if __name__ == "__main__":
    sys.exit(main())
