#!/usr/bin/env python3
# py-rules-ok: exact polynomial arithmetic for one worked example, about a minute
"""Check the worked confluence example at c = 0, lambda = 0, N = 5.

Torus paper, Section 7 (example after Theorem 7.4), and sphere paper,
Section 4 (example after Theorem 4.7).  At b_star^2 = -3/2 (c = 0) the labels
(1,1) and (1,2) both have weight 0.  With the generic residue data of the
papers (torus Definition 6.1, sphere Definition 4.1) the script checks:

  1. the labels with rs <= 5 and weight 0 at b_star are (1,1) and (1,2);
  2. every A_{r,s} with rs <= 5 is finite and nonzero at b_star;
  3. in the recursion trees of S_{(1,1),4} and S_{(1,2),3} exactly two shifted
     denominators vanish at b_star: z_{(1,1)} - h_{1,4} and z_{(1,2)} - h_{3,1};
  4. the derivatives satisfy h'_{1,4} = 5 h'_{1,2} and h'_{3,1} = -6 h'_{1,2};
  5. the simple poles of B_{(1,1),5} and B_{(1,2),5} are -R11 R14/(h'14 u) and
     R12 R31/((h'12 - h'31) u), and they cancel;
  6. the second collision moment equals R12 R31/7 = R11 R14/5, which is
     -(3/11200) P11 P14 (torus) and -(3/11200) phi(D4,D3) phi(D1,D2) with
     phi = P11 P14 (sphere), the top-layer value with gamma_2^- = -11200/3;
  7. that value equals the coefficient of Delta^{-2} in H_5 computed directly
     from the Gram matrices (sphere/tools/exact_sphere_block.py), and for the
     torus from the Shapovalov and torus matrices (tools/exact_shapovalov.py,
     only with --torus-direct, slower).

The expansions use the local coordinate u = b^2 - b_star^2, in which all data
are rational.  Poles and derivatives are taken in u; the statements 4-6 hold
in t = b - b_star as well, since du/dt = 2 b_star at t = 0 multiplies every
residue and every derivative by the same factor, and the grouped moments do
not depend on the coordinate (sphere Remark 4.8).

Usage: python3 -u tools/check_c0_level5_example.py [--torus-direct]
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from fractions import Fraction as Fr

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
N = 5
NU0 = Fr(-3, 2)  # b_star^2 at (p, p') = (2, 3), c = 0
PREC = 6  # keep powers u^k with k <= PREC
d = sp.symbols("d")
T0 = time.time()


def log(message):
    stamp = time.strftime("%H:%M:%SZ", time.gmtime())
    print(f"{stamp} +{time.time() - T0:6.1f}s {message}", flush=True)


def check(name, ok):
    log(("[PASS] " if ok else "[FAIL] ") + name)
    if not ok:
        sys.exit(1)


# ---- truncated Laurent series in u with coefficients sympy Poly in d ----

ZERO = sp.Poly(0, d, domain="QQ")
ONE = sp.Poly(1, d, domain="QQ")


def const(x):
    if isinstance(x, sp.Poly):
        return x
    if isinstance(x, Fr):
        x = sp.Rational(x.numerator, x.denominator)
    return sp.Poly(x, d, domain="QQ")


def s_clean(s):
    return {k: v for k, v in s.items() if k <= PREC and not v.is_zero}


def s_add(*ss):
    out = {}
    for s in ss:
        for k, v in s.items():
            out[k] = out.get(k, ZERO) + v
    return s_clean(out)


def s_mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            if i + j <= PREC:
                out[i + j] = out.get(i + j, ZERO) + x * y
    return s_clean(out)


def s_scale(a, c):
    c = const(c)
    return s_clean({k: v * c for k, v in a.items()})


def s_val(a):
    return min(a) if a else None


def s_inv(a):
    """Inverse of a series whose lowest coefficient is a nonzero constant."""
    v = s_val(a)
    lead = a[v]
    assert lead.is_ground and not lead.is_zero, "inverse needs a constant leading coefficient"
    lead_inv = sp.Rational(1) / lead.as_expr()
    # a = lead u^v (1 + w), w has positive powers
    w = {k - v: s_scale({0: c}, lead_inv)[0] for k, c in a.items() if k != v}
    w = s_clean(w)
    # 1/(1+w) = sum_n (-w)^n
    inv = {0: ONE}
    power = {0: ONE}
    neg_w = s_scale(w, -1)
    for _ in range(PREC - v + 2):
        power = s_mul(power, neg_w)
        if not power:
            break
        inv = s_add(inv, power)
    shifted = {k - v: c for k, c in inv.items()}
    return s_scale(s_clean(shifted), lead_inv)


def nu_series():
    return s_clean({0: const(NU0), 1: ONE})


def nu_pow(k):
    nu = nu_series()
    if k >= 0:
        out = {0: ONE}
        for _ in range(k):
            out = s_mul(out, nu)
        return out
    inv = s_inv(nu)
    out = {0: ONE}
    for _ in range(-k):
        out = s_mul(out, inv)
    return out


def laurent_nu(expr_coeffs):
    """Series of sum_k c_k nu^k (c_k Poly in d)."""
    return s_add(*[s_scale(nu_pow(k), c) for k, c in expr_coeffs.items()])


# ---- data of the papers, as functions of nu = b^2 ----

def kac_series(r, s):
    # h_{r,s} = ((1 - r^2) nu + 2 (1 - rs) + (1 - s^2)/nu) / 4
    return laurent_nu({1: const(Fr(1 - r * r, 4)), 0: const(Fr(2 * (1 - r * s), 4)),
                       -1: const(Fr(1 - s * s, 4))})


def kac_star(r, s):
    return Fr((3 * r - 2 * s) ** 2 - 1, 24)


def A_series(r, s):
    # A_{r,s} = (1/2) nu^{2rs-1} prod (m nu + n)^{-1}
    out = s_scale(nu_pow(2 * r * s - 1), Fr(1, 2))
    for m in range(1 - r, r + 1):
        for n in range(1 - s, s + 1):
            if (m, n) in ((0, 0), (r, s)):
                continue
            out = s_mul(out, s_inv(s_clean({0: const(m * NU0 + n), 1: const(m)})))
    return out


def P_torus_series(r, s):
    # prod over odd k, l of (Lam^2 - (k b + l/b)^2)/4 (Lam^2 - (k b - l/b)^2)/4,
    # Lam^2 = nu + 2 + 1/nu - 4d, (k b +- l/b)^2 = k^2 nu +- 2kl + l^2/nu
    out = {0: ONE}
    for k in range(1, 2 * r, 2):
        for l in range(1, 2 * s, 2):
            for sign in (1, -1):
                fac = laurent_nu({1: const(Fr(1 - k * k, 4)),
                                  0: sp.Poly(sp.Rational(2 - 2 * sign * k * l, 4) - d, d, domain="QQ"),
                                  -1: const(Fr(1 - l * l, 4))})
                out = s_mul(out, fac)
    return out


def P_sphere_series(r, s, Da, Db):
    # pair (j,l) with (-j,-l): ((La+Lb)^2 - X^2)/4 * ((La-Lb)^2 - X^2)/4 / ... ; write via
    # (La+Lb+X)(La-Lb+X)(La+Lb-X)(La-Lb-X)/16 = ((La^2 - Lb^2 + X^2)^2 - 4 La^2 X^2)/16,
    # X^2 = (j b + l/b)^2 = j^2 nu + 2jl + l^2/nu, La^2 = Q^2 - 4 Da, La^2 - Lb^2 = 4 (Db - Da).
    q2 = laurent_nu({1: ONE, 0: const(2), -1: ONE})
    la2 = s_add(q2, {0: const(-4 * Da)})
    diff = {0: const(4 * (Db - Da))}
    out = {0: ONE}
    seen = set()
    for j in range(1 - r, r, 2):
        for l in range(1 - s, s, 2):
            if (j, l) in seen:
                continue
            if (j, l) == (0, 0):
                out = s_mul(out, {0: const(Db - Da)})
                seen.add((0, 0))
                continue
            x2 = laurent_nu({1: const(j * j), 0: const(2 * j * l), -1: const(l * l)})
            sq = s_add(diff, x2)
            fac = s_add(s_mul(sq, sq), s_scale(s_mul(la2, x2), -4))
            out = s_mul(out, s_scale(fac, Fr(1, 16)))
            seen.add((j, l))
            seen.add((-j, -l))
    return out


LABELS = [(r, s) for r in range(1, N + 1) for s in range(1, N + 1) if r * s <= N]
KAC = {g: kac_series(*g) for g in LABELS}


def zero_denominators(a, level, found):
    za = kac_star(*a) + a[0] * a[1]
    for g in LABELS:
        lg = g[0] * g[1]
        if lg > level:
            continue
        if za - kac_star(*g) == 0:
            found.append((a, g, level))
        zero_denominators(g, level - lg, found)


def shifted_block(a, level, residues, cache):
    """S_{a,level}(u) by the shifted recursion of torus Def. 7.1 / sphere Def. 4.5."""
    key = (a, level)
    if key in cache:
        return cache[key]
    if level == 0:
        cache[key] = {0: ONE}
        return cache[key]
    za = s_add(KAC[a], {0: const(a[0] * a[1])})
    total = {}
    for g in LABELS:
        lg = g[0] * g[1]
        if lg > level:
            continue
        denom = s_add(za, s_scale(KAC[g], -1))
        term = s_mul(s_mul(residues[g], s_inv(denom)), shifted_block(g, level - lg, residues, cache))
        total = s_add(total, term)
    cache[key] = total
    return total


def coef(s, k):
    return s.get(k, ZERO)


def run_case(name, residues, top_value, direct_value, direct_first=None):
    log(f"--- {name}")
    cache = {}
    B11 = s_mul(residues[(1, 1)], shifted_block((1, 1), N - 1, residues, cache))
    B12 = s_mul(residues[(1, 2)], shifted_block((1, 2), N - 2, residues, cache))
    log(f"  expanded B_(1,1),5 (valuation {s_val(B11)}) and B_(1,2),5 (valuation {s_val(B12)})")
    dh = {g: coef(KAC[g], 1) for g in [(1, 2), (1, 4), (3, 1)]}
    r0 = {g: coef(residues[g], 0) for g in [(1, 1), (1, 2), (1, 4), (3, 1)]}
    check(f"{name}: B_(1,1),5 and B_(1,2),5 have simple poles", s_val(B11) == -1 and s_val(B12) == -1)
    alpha, alpha_p = coef(B11, -1), coef(B12, -1)
    check(f"{name}: pole of B_(1,1) is -R11 R14/(h'14 u)",
          (alpha * dh[(1, 4)] + r0[(1, 1)] * r0[(1, 4)]).is_zero)
    check(f"{name}: pole of B_(1,2) is R12 R31/((h'12 - h'31) u)",
          (alpha_p * (dh[(1, 2)] - dh[(3, 1)]) - r0[(1, 2)] * r0[(3, 1)]).is_zero)
    check(f"{name}: the two poles cancel", (alpha + alpha_p).is_zero)
    delta12 = KAC[(1, 2)]
    check(f"{name}: delta_(1,1) = h_(1,1) is identically 0", not KAC[(1, 1)])
    second = coef(s_mul(B12, delta12), 0)
    first = coef(s_add(B11, B12), 0)
    check(f"{name}: second moment = R12 R31/7", (7 * second - r0[(1, 2)] * r0[(3, 1)]).is_zero)
    check(f"{name}: second moment = R11 R14/5", (5 * second - r0[(1, 1)] * r0[(1, 4)]).is_zero)
    check(f"{name}: second moment = top-layer value -(3/11200) phi phi", (second - top_value).is_zero)
    if direct_value is not None:
        check(f"{name}: second moment = direct [Delta^-2] H_5", (second - const(direct_value)).is_zero)
    if direct_first is not None:
        check(f"{name}: first moment = direct [Delta^-1] H_5", (first - const(direct_first)).is_zero)
    log(f"  second moment = {second.as_expr()}")
    log(f"  first moment  = {sp.factor(first.as_expr())}")


def sphere_direct(dext):
    sys.path.insert(0, os.path.join(ROOT, "sphere", "tools"))
    import exact_sphere_block as esb  # noqa: E402

    _, H_funcs, _, _, _ = esb.check_minimal_model(2, 3, 1, 1, 5, dext)
    order, coeffs = H_funcs[5].laurent_at(Fr(0), 0)
    assert order == 2
    return coeffs[-2], coeffs[-1]


def torus_direct():
    sys.path.insert(0, HERE)
    import exact_shapovalov as es  # noqa: E402

    _, hs = es.h_coefficients(5, sp.Integer(0))
    expr = sp.cancel(hs[5] * es.h**2)
    second = sp.expand(expr.subs(es.h, 0))
    first = sp.expand(sp.diff(expr, es.h).subs(es.h, 0))
    return (sp.Poly(second.subs(es.d, d), d, domain="QQ"), sp.Poly(first.subs(es.d, d), d, domain="QQ"))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--torus-direct", action="store_true",
                        help="also compute torus H_5 at c = 0 from the Shapovalov matrices (slower)")
    args = parser.parse_args()

    weight0 = [a for a in LABELS if kac_star(*a) == 0]
    check("labels of weight 0 with rs <= 5 are (1,1), (1,2)", weight0 == [(1, 1), (1, 2)])
    check("Kac series agree with the closed form at u = 0",
          all(coef(KAC[g], 0) == const(kac_star(*g)) for g in LABELS))
    A = {g: A_series(*g) for g in LABELS}
    check("every A_{r,s} with rs <= 5 is regular and nonzero at b_star",
          all(s_val(A[g]) == 0 for g in LABELS))
    check("A_{1,1} = 1/2 and A_{1,4}(b_star) = -3/1120",
          coef(A[(1, 1)], 0) == const(Fr(1, 2)) and coef(A[(1, 4)], 0) == const(Fr(-3, 1120)))
    found = []
    zero_denominators((1, 1), 4, found)
    zero_denominators((1, 2), 3, found)
    check("vanishing shifted denominators: (1,1)-(1,4) and (1,2)-(3,1) only",
          sorted(set(found)) == [((1, 1), (1, 4), 4), ((1, 2), (3, 1), 3)])
    d12, d14, d31 = (coef(KAC[g], 1) for g in [(1, 2), (1, 4), (3, 1)])
    check("h'14 = 5 h'12 and h'31 = -6 h'12", (d14 - 5 * d12).is_zero and (d31 + 6 * d12).is_zero)

    # Torus, d indeterminate.
    PT = {g: P_torus_series(*g) for g in LABELS}
    res_t = {g: s_mul(A[g], PT[g]) for g in LABELS}
    top_t = coef(PT[(1, 1)], 0) * coef(PT[(1, 4)], 0) * const(Fr(-3, 11200))
    roots = [Fr(x * x - 1, 24) for x in (1, 5)], [Fr(x * x - 1, 24) for x in (1, 3, 5, 7, 9, 11, 13, 17)]
    check("torus P_{1,1}, P_{1,4} at b_star are monic with roots (x^2-1)/24, x in {1,5} and {1,3,...,17}",
          coef(PT[(1, 1)], 0) == sp.Poly(sp.prod([d - sp.Rational(r.numerator, r.denominator) for r in roots[0]]), d, domain="QQ")
          and coef(PT[(1, 4)], 0) == sp.Poly(sp.prod([d - sp.Rational(r.numerator, r.denominator) for r in roots[1]]), d, domain="QQ"))
    direct_t = torus_direct() if args.torus_direct else (None, None)
    run_case("torus", res_t, top_t, direct_t[0], direct_t[1])

    # Sphere, rational external weights; the first tuple is the one of
    # exact_sphere_block.check_ribault_23_N5.
    samples = [[Fr(1, 7), Fr(2, 7), Fr(3, 7), Fr(5, 7)],
               [Fr(2, 3), Fr(1, 5), Fr(4, 11), Fr(3, 13)],
               [Fr(5, 9), Fr(7, 4), Fr(1, 6), Fr(8, 15)]]
    for idx, avals in enumerate(samples):
        dext = tuple(Fr(3, 2) * x * x - Fr(1, 24) for x in avals)
        D1, D2, D3, D4 = dext
        res_s = {g: s_mul(A[g], s_mul(P_sphere_series(*g, D4, D3), P_sphere_series(*g, D1, D2))) for g in LABELS}
        phi43 = coef(P_sphere_series(1, 1, D4, D3), 0) * coef(P_sphere_series(1, 4, D4, D3), 0)
        phi12 = coef(P_sphere_series(1, 1, D1, D2), 0) * coef(P_sphere_series(1, 4, D1, D2), 0)
        top_s = phi43 * phi12 * const(Fr(-3, 11200))
        direct_s = sphere_direct(dext)
        run_case(f"sphere sample {idx + 1}", res_s, top_s, direct_s[0], direct_s[1])
    log("all checks passed")


if __name__ == "__main__":
    main()
