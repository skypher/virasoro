#!/usr/bin/env python3
"""Exact low-grade replay of the all-order collision-moment recursion."""

from functools import lru_cache

import sympy as sp

from exact_shapovalov import d, h, h_coefficients


b = sp.symbols("b")
internal = sp.symbols("internal")
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
    return result


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


@lru_cache(maxsize=None)
def residue(r, s):
    return sp.cancel(residue_constant(r, s) * fusion_polynomial(r, s))


def labels(maximum_level):
    result = []
    for r in range(1, maximum_level + 1):
        for s in range(1, maximum_level // r + 1):
            result.append((r, s))
    return result


@lru_cache(maxsize=None)
def shifted(r, s, grade):
    if grade == 0:
        return sp.Integer(1)
    source_weight = kac_weight(r, s) + r * s
    result = sp.Integer(0)
    for u, v in labels(grade):
        level = u * v
        result += (
            residue(u, v)
            * shifted(u, v, grade - level)
            / (source_weight - kac_weight(u, v))
        )
    return sp.cancel(result)


def check_equal(name, actual, expected):
    difference = sp.factor(sp.cancel(actual - expected))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    print(f"PASS {name}", flush=True)


def main():
    _, direct_reduced = h_coefficients(2)

    reconstructed_two = sp.Integer(0)
    for r, s in labels(2):
        level = r * s
        coefficient = residue(r, s) * shifted(r, s, 2 - level)
        reconstructed_two += coefficient.subs(b, b0) / (
            internal - kac_weight(r, s).subs(b, b0)
        )
    check_equal(
        "collision-moment recursion at level 2",
        reconstructed_two,
        direct_reduced[2].subs(h, internal),
    )

    collision = sp.Rational(1, 16)
    b_12 = residue(1, 2) * shifted(1, 2, 2)
    b_22 = residue(2, 2)
    first_moment = sp.factor((b_12 + b_22).subs(b, b0))
    second_moment = sp.factor(
        (
            b_12 * (kac_weight(1, 2) - collision)
            + b_22 * (kac_weight(2, 2) - collision)
        ).subs(b, b0)
    )

    p2 = (
        d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 4
    )
    p4 = (
        d
        * (d - 1)
        * (2 * d - 7)
        * (2 * d - 1)
        * (3 * d - 14)
        * (3 * d - 5)
        * (6 * d - 55)
        * (6 * d - 1)
        / 1296
    )
    expected_first = (
        sp.Rational(-4, 7)
        * p2
        * direct_reduced[2].subs(h, sp.Rational(33, 16))
        + sp.Rational(648, 13475) * p4
    )
    check_equal(
        "spin collision moment at level 4",
        first_moment,
        expected_first,
    )
    check_equal(
        "vanishing second spin-collision moment at level 4",
        second_moment,
        0,
    )


if __name__ == "__main__":
    main()
