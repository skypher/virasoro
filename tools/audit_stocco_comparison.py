#!/usr/bin/env python3
"""Imported identities and comparison with Stocco's pole-free expressions.

Verifies, in exact arithmetic:

  * the fusion-normalization identity of the paper at a generic sample
    point b = 2 for the labels (2,1) and (1,2), by solving for the
    normalized level-two singular vector from scratch;
  * the crossing-normalization identity of the paper at b_0 for the labels
    (2,1), (1,3), (1,2), (2,2): the inverse generic residue constants
    equal the crossing scalars 28/9, -105/8, -7/4, 13475/648 verified
    from Gram-matrix derivatives by the other audit scripts;
  * that the pole-free numerators of Stocco (arXiv:2209.08653):
    K_2 (eq. II.11) and K_3 (eq. A.2) reproduce the generic blocks H_2
    and H_3 identically in b, and that K_4 (eq. A.3) reproduces H_4 at
    the Ising point b_0 (pass --full to also check K_4 at b = 2, 3).
    Conventions: beta = b^2, Delta_1 = d.
"""

import argparse
import sys

import sympy as sp

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from exact_shapovalov import h, d, level_matrices, euler_coefficients

b, beta = sp.symbols("b beta")
B0 = 2 * sp.I / sp.sqrt(3)
D1 = d


def check_equal(name, actual, expected):
    difference = sp.simplify(sp.cancel(sp.together(actual - expected)))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    print(f"PASS {name}", flush=True)


def kac_weight(r, s, bb=b):
    return sp.cancel(((bb + 1 / bb) ** 2 - (r * bb + s / bb) ** 2) / 4)


def residue_constant(r, s, bb=b):
    result = sp.Rational(1, 2)
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            result /= p * bb + q / bb
    return sp.cancel(result)


def fusion_polynomial(r, s, bb=b):
    lam2 = (bb + 1 / bb) ** 2 - 4 * d
    result = sp.Integer(1)
    for k in range(1, 2 * r, 2):
        for ell in range(1, 2 * s, 2):
            result *= (lam2 - (k * bb + ell / bb) ** 2) / 4
            result *= (lam2 - (k * bb - ell / bb) ** 2) / 4
    return result


def fusion_normalization_generic():
    """Fusion-normalization identity at the generic sample point b = 2."""
    bval = sp.Integer(2)
    cval = sp.expand(1 + 6 * (bval + 1 / bval) ** 2)
    for (r, s) in [(2, 1), (1, 2)]:
        weight = kac_weight(r, s, bval)
        _, gram, vertex = level_matrices(2, central_charge=cval)
        a = sp.symbols("a")
        vec = sp.Matrix([a, 1])
        gram_at = gram.subs(h, weight)
        sols = set(sp.solve((gram_at * vec)[0], a))
        sols &= set(sp.solve((gram_at * vec)[1], a))
        assert len(sols) == 1, (r, s)
        vec = vec.subs(a, sols.pop())
        element = sp.expand((vec.T * vertex.subs(h, weight) * vec)[0])
        check_equal(f"fusion normalization at generic b=2 for {(r, s)}",
                    element, fusion_polynomial(r, s, bval))


def crossing_normalization_ising():
    """Crossing-normalization identity at b_0 against the audited crossing scalars."""
    audited = {(2, 1): sp.Rational(28, 9), (1, 3): sp.Rational(-105, 8),
               (1, 2): sp.Rational(-7, 4), (2, 2): sp.Rational(13475, 648)}
    for label, scalar in audited.items():
        check_equal(f"crossing normalization at b_0 for {label}",
                    1 / residue_constant(*label, bb=B0), scalar)


def stocco_K2():
    c_sym = sp.symbols("c")
    return (D1 * (D1 - 1) / 2) / 32 * (
        96 * h**2
        + 4 * h * (-14 * D1 + 2 * D1**2 + 5 + c_sym)
        + c_sym * D1 * (D1 - 1)), c_sym


def stocco_K3():
    cb2 = (144 * h + 288 * h**2 - 144 * h * D1 + 48 * (D1 - 1) * D1
           + 144 * h * D1**2 - 12 * (D1 - 1) * D1**2
           + 12 * (D1 - 1) * D1**3)
    cb1 = (888 * h + 960 * h**3 - 1840 * h * D1 + 440 * (D1 - 1) * D1
           + 1574 * h * D1**2 - 164 * (D1 - 1) * D1**2 - 332 * h * D1**3
           + 68 * (D1 - 1) * D1**3 + 22 * h * D1**4
           + 24 * h**2 * (76 - 75 * D1 + 27 * D1**2))
    cb0 = (1536 * h + 768 * h**4 - 3232 * h * D1 + 824 * (D1 - 1) * D1
           + 2535 * h * D1**2 - 323 * (D1 - 1) * D1**2 - 590 * h * D1**3
           + 115 * (D1 - 1) * D1**3 + 39 * h * D1**4
           + 96 * h**3 * (24 - 19 * D1 + 3 * D1**2)
           + 8 * h**2 * (342 - 411 * D1 + 238 * D1**2 - 20 * D1**3
                         + D1**4))
    Bj = lambda j: beta**j + beta**(-j)
    return (cb2 * Bj(2) + cb1 * Bj(1) + cb0) / 192


def stocco_K4():
    Bj = lambda j: beta**j + beta**(-j)
    cb4 = (96 * h + 288 * h**2 + 192 * h**3 - 36 * D1 - 168 * h * D1
           - 144 * h**2 * D1 + 52 * D1**2 + 192 * h * D1**2
           + 144 * h**2 * D1**2 - 33 * D1**3 - 48 * h * D1**3 + 19 * D1**4
           + 24 * h * D1**4 - 3 * D1**5 + D1**6)
    cb3 = (45120 * h + 141600 * h**2 + 132000 * h**3 + 41280 * h**4
           - 14652 * D1 - 92604 * h * D1 - 136152 * h**2 * D1
           - 61392 * h**3 * D1 + 27284 * D1**2 + 109180 * h * D1**2
           + 105984 * h**2 * D1**2 + 26832 * h**3 * D1**2 - 22281 * D1**3
           - 49095 * h * D1**3 - 26064 * h**2 * D1**3 + 11363 * D1**4
           + 16885 * h * D1**4 + 4392 * h**2 * D1**4 - 2091 * D1**5
           - 1749 * h * D1**5 + 377 * D1**6 + 103 * h * D1**6)
    cb2 = (1423008 * h + 4167168 * h**2 + 4189536 * h**3 + 2013312 * h**4
           + 446976 * h**5 - 442908 * D1 - 3093480 * h * D1
           - 5225328 * h**2 * D1 - 3529776 * h**3 * D1 - 993408 * h**4 * D1
           + 914364 * D1**2 + 3900600 * h * D1**2 + 4702504 * h**2 * D1**2
           + 2296944 * h**3 * D1**2 + 336768 * h**4 * D1**2 - 799689 * D1**3
           - 2092518 * h * D1**3 - 1684440 * h**2 * D1**3
           - 450048 * h**3 * D1**3 + 391899 * D1**4 + 673314 * h * D1**4
           + 343312 * h**2 * D1**4 + 41280 * h**3 * D1**4 - 74427 * D1**5
           - 84018 * h * D1**5 - 20280 * h**2 * D1**5 + 10761 * D1**6
           + 4902 * h * D1**6 + 712 * h**2 * D1**6)
    cb1 = (1683456 * h**6 + 3072 * h**5 * (3292 - 1669 * D1 + 409 * D1**2)
           + 768 * h**4 * (45703 - 32773 * D1 + 17503 * D1**2
                           - 2532 * D1**3 + 162 * D1**4)
           + 9 * D1 * (-734868 + 1587868 * D1 - 1423299 * D1**2
                       + 684065 * D1**3 - 130937 * D1**4 + 17171 * D1**5)
           + 64 * h**3 * (978855 - 1016103 * D1 + 729839 * D1**2
                          - 190791 * D1**3 + 25799 * D1**4 - 1023 * D1**5
                          + 29 * D1**6)
           + 8 * h**2 * (7271424 - 10546749 * D1 + 10186433 * D1**2
                         - 3976128 * D1**3 + 840752 * D1**4
                         - 61824 * D1**5 + 2156 * D1**6)
           + 3 * h * (7167168 - 15881724 * D1 + 20837492 * D1**2
                      - 11935235 * D1**3 + 3761009 * D1**4
                      - 491001 * D1**5 + 28819 * D1**6))
    cb0 = (28999296 * h + 75605760 * h**2 + 85087104 * h**3
           + 47781120 * h**4 + 15793152 * h**5 + 2617344 * h**6
           + 344064 * h**7 - 8901576 * D1 - 64431288 * h * D1
           - 115515792 * h**2 * D1 - 92818272 * h**3 * D1
           - 38587392 * h**4 * D1 - 8169984 * h**5 * D1
           - 1314816 * h**6 * D1 + 19491840 * D1**2 + 85511472 * h * D1**2
           + 114226816 * h**2 * D1**2 + 68972000 * h**3 * D1**2
           + 20325120 * h**4 * D1**2 + 3518976 * h**5 * D1**2
           + 208896 * h**6 * D1**2 - 17583363 * D1**3 - 49771617 * h * D1**3
           - 45926220 * h**2 * D1**3 - 18616256 * h**3 * D1**3
           - 3539200 * h**4 * D1**3 - 344064 * h**5 * D1**3
           + 8397441 * D1**4 + 15592539 * h * D1**4
           + 9878804 * h**2 * D1**4 + 2576704 * h**3 * D1**4
           + 314880 * h**4 * D1**4 + 18432 * h**5 * D1**4 - 1609353 * D1**5
           - 2056035 * h * D1**5 - 775652 * h**2 * D1**5
           - 102976 * h**3 * D1**5 - 9984 * h**4 * D1**5 + 205011 * D1**6
           + 121329 * h * D1**6 + 26924 * h**2 * D1**6 + 2880 * h**3 * D1**6
           + 256 * h**4 * D1**6)
    return (sp.Rational(45, 2048) * cb4 * Bj(4)
            + sp.Rational(3, 4096) * cb3 * Bj(3)
            + sp.Rational(1, 8192) * cb2 * Bj(2)
            + sp.Rational(1, 49152) * cb1 * Bj(1)
            + sp.Rational(1, 49152) * cb0)


def our_H(max_level, central_charge):
    coefficients = [sp.Integer(1)]
    for level in range(1, max_level + 1):
        _, gram, vertex = level_matrices(level, central_charge=central_charge)
        coefficients.append(
            sp.cancel(sp.trace(gram.inv(method="GE") * vertex.T)))
    euler = euler_coefficients(max_level)
    return sp.cancel(sum(euler[max_level - j] * coefficients[j]
                         for j in range(max_level + 1)))


LABELS = {2: [(1, 1), (2, 1), (1, 2)],
          3: [(1, 1), (2, 1), (1, 2), (3, 1), (1, 3)],
          4: [(1, 1), (2, 1), (1, 2), (3, 1), (1, 3), (4, 1), (1, 4),
              (2, 2)]}


def compare_generic(order, numerator, tag):
    c_sym = sp.symbols("c")
    den = sp.prod([h - kac_weight(r, s) for (r, s) in LABELS[order]])
    lhs = sp.cancel(numerator.subs(beta, b**2) / den)
    rhs = our_H(order, c_sym).subs(c_sym, 1 + 6 * (b + 1 / b) ** 2)
    check_equal(tag, lhs, rhs)


def compare_at_point(order, numerator, bval, tag):
    cval = sp.nsimplify(sp.expand(1 + 6 * (bval + 1 / bval) ** 2))
    den = sp.prod([h - sp.nsimplify(kac_weight(r, s, bval))
                   for (r, s) in LABELS[order]])
    lhs = sp.cancel(sp.nsimplify(numerator.subs(beta, bval**2)) / den)
    check_equal(tag, lhs, our_H(order, cval))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true",
                        help="also check K_4 at generic points b = 2, 3")
    args = parser.parse_args()

    fusion_normalization_generic()
    crossing_normalization_ising()

    k2_expr, c_sym = stocco_K2()
    den2 = sp.prod([h - kac_weight(r, s) for (r, s) in LABELS[2]])
    lhs2 = sp.cancel(
        k2_expr.subs(c_sym, 1 + 6 * (b + 1 / b) ** 2) / den2)
    rhs2 = our_H(2, c_sym).subs(c_sym, 1 + 6 * (b + 1 / b) ** 2)
    check_equal("Stocco order 2 (II.11), identically in b", lhs2, rhs2)

    k3 = (D1 * (D1 - 1) / 2) * stocco_K3()
    compare_generic(3, k3, "Stocco order 3 (A.2), identically in b")

    k4 = (D1 * (D1 - 1) / 2) * stocco_K4()
    compare_at_point(4, k4, B0,
                     "Stocco order 4 (A.3) at the Ising point b_0")
    if args.full:
        for bval in (sp.Integer(2), sp.Integer(3)):
            compare_at_point(4, k4, bval,
                             f"Stocco order 4 (A.3) at b={bval}")


if __name__ == "__main__":
    main()
