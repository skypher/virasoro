#!/usr/bin/env python3
"""Exact audit of the first Ising confluence at total level ten."""

import sympy as sp


b = sp.symbols("b")
d = sp.symbols("d")
b0 = 2 * sp.I / sp.sqrt(3)


def kac_weight(r, s):
    q = b + 1 / b
    return sp.expand((q**2 - (r * b + s / b) ** 2) / 4)


def residue_constant(r, s):
    result = sp.Rational(1, 2)
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            result /= p * b + q / b
    return sp.factor(result.subs(b, b0))


def fusion_polynomial(r, s):
    q = b + 1 / b
    momentum_squared = q**2 - 4 * d
    result = sp.Integer(1)
    for k in range(1, 2 * r, 2):
        for ell in range(1, 2 * s, 2):
            result *= (
                momentum_squared - (k * b + ell / b) ** 2
            ) / 4
            result *= (
                momentum_squared - (k * b - ell / b) ** 2
            ) / 4
    return result


def residue_polynomial(r, s):
    return residue_constant_family(r, s) * fusion_polynomial(r, s)


def residue_constant_family(r, s):
    result = sp.Rational(1, 2)
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            result /= p * b + q / b
    return result


def nested_finite_term(parent, child, delta):
    parent_residue = residue_polynomial(*parent)
    child_residue = residue_polynomial(*child)
    parent_value = parent_residue.subs(b, b0)
    child_value = child_residue.subs(b, b0)
    delta_one = sp.diff(delta, b).subs(b, b0)
    delta_two = sp.diff(delta, b, 2).subs(b, b0)
    return sp.together(
        (
            sp.diff(parent_residue, b).subs(b, b0) * child_value
            + parent_value * sp.diff(child_residue, b).subs(b, b0)
        )
        / delta_one
        - parent_value
        * child_value
        * delta_two
        / (2 * delta_one**2)
    )


def check_equal(name, actual, expected):
    difference = sp.factor(sp.simplify(actual - expected))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    print(f"PASS {name}", flush=True)


def main():
    h12 = kac_weight(1, 2)
    h22 = kac_weight(2, 2)
    h42 = kac_weight(4, 2)
    h16 = kac_weight(1, 6)

    check_equal("h_12 at Ising point", h12.subs(b, b0), sp.Rational(1, 16))
    check_equal("h_22 at Ising point", h22.subs(b, b0), sp.Rational(1, 16))
    check_equal("h_42 at Ising point", h42.subs(b, b0), sp.Rational(33, 16))
    check_equal("h_16 at Ising point", h16.subs(b, b0), sp.Rational(65, 16))

    derivative = lambda expression: sp.diff(expression, b).subs(b, b0)
    slope_left = sp.simplify(
        (derivative(h12) - derivative(h22))
        / (derivative(h12) - derivative(h42))
    )
    slope_right = sp.simplify(
        (derivative(h22) - derivative(h12))
        / (derivative(h22) - derivative(h16))
    )
    check_equal("left confluence slope", slope_left, sp.Rational(1, 5))
    check_equal("right confluence slope", slope_right, sp.Rational(1, 7))

    a12 = residue_constant(1, 2)
    a22 = residue_constant(2, 2)
    a42 = residue_constant(4, 2)
    a16 = residue_constant(1, 6)
    check_equal("A_12", a12, sp.Rational(-4, 7))
    check_equal("A_22", a22, sp.Rational(648, 13475))
    check_equal("A_42", a42, sp.Rational(48, 32035128125))
    check_equal("A_16", a16, sp.Rational(-8, 320945625))

    inverse_second_crossing = sp.Rational(-192, 1121229484375)
    check_equal(
        "left nested residue",
        slope_left * a12 * a42,
        inverse_second_crossing,
    )
    check_equal(
        "right nested residue",
        slope_right * a22 * a16,
        inverse_second_crossing,
    )
    check_equal(
        "second crossing scalar",
        1 / inverse_second_crossing,
        sp.Rational(-1121229484375, 192),
    )

    fusion_42 = sp.factor(fusion_polynomial(4, 2).subs(b, b0))
    fusion_16 = sp.factor(fusion_polynomial(1, 6).subs(b, b0))
    expected_fusion_42 = (
        d
        * (d - 20)
        * (d - 13)
        * (d - 11)
        * (d - 6)
        * (d - 1)
        * (2 * d - 57)
        * (2 * d - 35)
        * (2 * d - 15)
        * (2 * d - 7)
        * (2 * d - 5)
        * (2 * d - 1)
        * (3 * d - 14)
        * (3 * d - 5)
        * (6 * d - 55)
        * (6 * d - 1)
        / 20736
    )
    expected_fusion_16 = (
        d
        * (d - 20)
        * (d - 13)
        * (d - 11)
        * (d - 6)
        * (d - 1)
        * (2 * d - 57)
        * (2 * d - 35)
        * (2 * d - 15)
        * (2 * d - 7)
        * (2 * d - 5)
        * (2 * d - 1)
        / 64
    )
    check_equal("level-8 child fusion polynomial", fusion_42, expected_fusion_42)
    check_equal("level-6 child fusion polynomial", fusion_16, expected_fusion_16)
    check_equal(
        "fusion factorization around the diamond",
        fusion_polynomial(1, 2).subs(b, b0) * fusion_42,
        fusion_polynomial(2, 2).subs(b, b0) * fusion_16,
    )

    delta_left = h12 + 2 - h42
    delta_right = h22 + 4 - h16
    finite_nested = sp.factor(
        sp.cancel(
            nested_finite_term((1, 2), (4, 2), delta_left)
            + nested_finite_term((2, 2), (1, 6), delta_right)
        )
    )
    expected_finite_nested = (
        -d**2
        * (d - 1) ** 2
        * (2 * d - 7) ** 2
        * (2 * d - 1) ** 2
        * (3 * d - 14)
        * (3 * d - 5)
        * (6 * d - 55)
        * (6 * d - 1)
        * (
            424640464 * d**8
            - 41506307104 * d**7
            + 1664502727528 * d**6
            - 35552058801520 * d**5
            + 438148123547677 * d**4
            - 3142854705332170 * d**3
            + 12488401942129875 * d**2
            - 23870935242348750 * d
            + 14566042731240000
        )
        / 552735279561465000000
    )
    check_equal(
        "finite nested contribution to the simple pole",
        finite_nested,
        expected_finite_nested,
    )


if __name__ == "__main__":
    main()
