#!/usr/bin/env python3
"""Independent exact audit of the first Ising collision and diamond."""

from collections import defaultdict

import sympy as sp

from exact_shapovalov import (
    act_mode,
    c,
    d,
    gram_entry,
    h,
    h_coefficients,
    level_matrices,
    normal_order_negative,
    partitions,
)


CENTRAL_CHARGE = sp.Rational(1, 2)
ENERGY_WEIGHT = sp.Rational(1, 2)
b = sp.symbols("b")
b0 = 2 * sp.I / sp.sqrt(3)


def check_equal(name, actual, expected):
    difference = sp.factor(sp.cancel(actual - expected))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    print(f"PASS {name}", flush=True)


def gram_matrix(level):
    basis = list(partitions(level))
    gram = sp.Matrix(
        [
            [
                gram_entry(left, right).subs(c, CENTRAL_CHARGE)
                for right in basis
            ]
            for left in basis
        ]
    )
    return basis, gram


def check_singular(name, level, basis, vector, weight):
    for mode in range(1, level + 1):
        coefficients = defaultdict(lambda: sp.Integer(0))
        for scalar, partition in zip(vector, basis):
            word = tuple(-part for part in partition)
            for output_word, output_scalar in act_mode(mode, word).items():
                coefficients[output_word] += scalar * output_scalar.subs(
                    {c: CENTRAL_CHARGE, h: weight}
                )
        for coefficient in coefficients.values():
            if sp.factor(coefficient) != 0:
                raise AssertionError(
                    f"{name}: L_{mode} gives {sp.factor(coefficient)}"
                )
    print(f"PASS {name}", flush=True)


def compose(parent_basis, parent, child_basis, child, total_basis):
    coefficients = defaultdict(lambda: sp.Integer(0))
    for parent_scalar, parent_partition in zip(parent, parent_basis):
        parent_word = tuple(-part for part in parent_partition)
        for child_scalar, child_partition in zip(child, child_basis):
            child_word = tuple(-part for part in child_partition)
            for word, normal_scalar in normal_order_negative(
                child_word + parent_word
            ).items():
                coefficients[word] += (
                    parent_scalar * child_scalar * normal_scalar
                )
    return sp.Matrix(
        [
            sp.factor(
                coefficients.get(tuple(-part for part in partition), 0)
            )
            for partition in total_basis
        ]
    )


def kac_weight(r, s):
    q = b + 1 / b
    return sp.cancel((q**2 - (r * b + s / b) ** 2) / 4)


def ising_labels_at_weight(weight, maximum_level):
    result = []
    for r in range(1, maximum_level + 1):
        for s in range(1, maximum_level // r + 1):
            fixed_weight = sp.Rational((4 * r - 3 * s) ** 2 - 1, 48)
            if fixed_weight == weight:
                result.append((r, s))
    return result


def residue_constant(r, s):
    result = sp.Rational(1, 2)
    for p in range(1 - r, r + 1):
        for q in range(1 - s, s + 1):
            if (p, q) in ((0, 0), (r, s)):
                continue
            result /= p * b + q / b
    return sp.cancel(result)


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
    return sp.cancel(result)


def torus_form(level, weight, vector):
    _, _, vertex = level_matrices(level)
    return sp.factor((vector.T * vertex.subs(h, weight) * vector)[0])


def main():
    collision_classes = {}
    for r in range(1, 7):
        for s in range(1, 6 // r + 1):
            collision_classes.setdefault(abs(4 * r - 3 * s), []).append(
                (r, s)
            )
    repeated_classes = {
        index: labels
        for index, labels in collision_classes.items()
        if len(labels) > 1
    }
    expected_repeated = {
        1: [(1, 1), (2, 3)],
        2: [(1, 2), (2, 2)],
        5: [(1, 3), (2, 1)],
    }
    if repeated_classes != expected_repeated:
        raise AssertionError(
            f"unexpected collision classes below level 7: {repeated_classes}"
        )
    print("PASS exhaustive collision classes below level 7", flush=True)

    child_gap_checks = (
        (sp.Rational(33, 16), 7),
        (sp.Rational(65, 16), 5),
        (sp.Integer(1), 5),
    )
    for child_weight, maximum_level in child_gap_checks:
        labels = ising_labels_at_weight(child_weight, maximum_level)
        if labels:
            raise AssertionError(
                f"unexpected child Kac labels for weight {child_weight} "
                f"through level {maximum_level}: {labels}"
            )
    print("PASS child-module gaps used in first-double-pole proof", flush=True)

    basis_two, gram_two = gram_matrix(2)
    basis_three, gram_three = gram_matrix(3)
    basis_four, _ = gram_matrix(4)
    basis_five, _ = gram_matrix(5)

    xi_two = sp.Matrix([-sp.Rational(4, 3), 1])
    xi_three = sp.Matrix([sp.Rational(3, 4), -3, 1])
    phi_five = sp.Matrix(
        [45, -54, -45, sp.Rational(99, 4), 36, -15, 1]
    )
    phi_four = sp.Matrix(
        [
            -sp.Rational(152, 3),
            sp.Rational(88, 3),
            16,
            -sp.Rational(40, 3),
            1,
        ]
    )

    check_singular(
        "energy level-2 singular vector",
        2,
        basis_two,
        xi_two,
        ENERGY_WEIGHT,
    )
    check_singular(
        "energy level-3 singular vector",
        3,
        basis_three,
        xi_three,
        ENERGY_WEIGHT,
    )
    check_singular(
        "level-5 child singular vector",
        5,
        basis_five,
        phi_five,
        sp.Rational(5, 2),
    )
    check_singular(
        "level-4 child singular vector",
        4,
        basis_four,
        phi_four,
        sp.Rational(7, 2),
    )

    check_equal(
        "energy level-2 crossing scalar",
        (xi_two.T * gram_two.diff(h).subs(h, ENERGY_WEIGHT) * xi_two)[0],
        sp.Rational(28, 9),
    )
    check_equal(
        "energy level-3 crossing scalar",
        (
            xi_three.T
            * gram_three.diff(h).subs(h, ENERGY_WEIGHT)
            * xi_three
        )[0],
        -sp.Rational(105, 8),
    )
    descendant_three = sp.Matrix(
        [-sp.Rational(4, 3), -sp.Rational(4, 3), 1]
    )
    kernel_three = sp.Matrix.hstack(descendant_three, xi_three)
    expected_crossing_three = sp.diag(
        sp.Rational(140, 9),
        -sp.Rational(105, 8),
    )
    if (
        kernel_three.T
        * gram_three.diff(h).subs(h, ENERGY_WEIGHT)
        * kernel_three
        != expected_crossing_three
    ):
        raise AssertionError("energy level-3 crossing matrix mismatch")
    print("PASS energy level-3 crossing matrix", flush=True)

    expected_e_two = (
        d * (d - 1) * (3 * d - 14) * (3 * d - 5) / 9
    )
    expected_e_three = (
        d
        * (d - 1)
        * (2 * d - 15)
        * (2 * d - 7)
        * (2 * d - 5)
        * (2 * d - 1)
        / 16
    )
    expected_e_five = (
        d
        * (d - 20)
        * (d - 13)
        * (d - 11)
        * (d - 6)
        * (d - 1)
        * (2 * d - 15)
        * (2 * d - 7)
        * (2 * d - 5)
        * (2 * d - 1)
        / 16
    )
    expected_e_four = (
        d
        * (d - 20)
        * (d - 13)
        * (d - 11)
        * (d - 6)
        * (d - 1)
        * (3 * d - 14)
        * (3 * d - 5)
        / 9
    )
    check_equal(
        "energy level-2 torus polynomial",
        torus_form(2, ENERGY_WEIGHT, xi_two),
        expected_e_two,
    )
    check_equal(
        "energy level-3 torus polynomial",
        torus_form(3, ENERGY_WEIGHT, xi_three),
        expected_e_three,
    )
    check_equal(
        "level-5 child torus polynomial",
        torus_form(5, sp.Rational(5, 2), phi_five),
        expected_e_five,
    )
    check_equal(
        "level-4 child torus polynomial",
        torus_form(4, sp.Rational(7, 2), phi_four),
        expected_e_four,
    )
    check_equal(
        "energy diamond fusion factorization",
        expected_e_two * expected_e_five,
        expected_e_three * expected_e_four,
    )

    _, reduced = h_coefficients(3)
    direct_residue_three = sp.factor(
        sp.limit(
            (h - ENERGY_WEIGHT) * reduced[3],
            h,
            ENERGY_WEIGHT,
        )
    )
    expected_residue_three = sp.factor(
        sp.Rational(9, 28)
        * expected_e_two
        * reduced[1].subs(h, sp.Rational(5, 2))
        - sp.Rational(8, 105) * expected_e_three
    )
    check_equal(
        "first fixed-c collided residue at level 3",
        direct_residue_three,
        expected_residue_three,
    )

    basis_seven, gram_seven = gram_matrix(7)
    left_image = compose(
        basis_two,
        xi_two,
        basis_five,
        phi_five,
        basis_seven,
    )
    right_image = compose(
        basis_three,
        xi_three,
        basis_four,
        phi_four,
        basis_seven,
    )
    if left_image != right_image:
        raise AssertionError("the two level-7 singular-vector images differ")
    print("PASS level-7 embedding diamond", flush=True)

    specialized = gram_seven.subs(h, ENERGY_WEIGHT)
    if specialized.rank() != 4:
        raise AssertionError(
            f"level-7 Gram rank is {specialized.rank()}, expected 4"
        )
    print("PASS level-7 Gram rank and radical dimension", flush=True)

    first_derivative = gram_seven.diff(h).subs(h, ENERGY_WEIGHT)
    kernel = sp.Matrix.hstack(*specialized.nullspace())
    first_crossing = kernel.T * first_derivative * kernel
    if first_crossing.rank() != 10:
        raise AssertionError(
            "level-7 first crossing rank is "
            f"{first_crossing.rank()}, expected 10"
        )
    print("PASS level-7 second Smith-layer dimension", flush=True)

    second_coefficient = (
        gram_seven.diff(h, 2).subs(h, ENERGY_WEIGHT) / 2
    )
    solution, parameters = specialized.gauss_jordan_solve(
        -first_derivative * left_image
    )
    correction = solution.subs({parameter: 0 for parameter in parameters})
    gamma_seven = sp.factor(
        (
            left_image.T
            * (
                second_coefficient * left_image
                + first_derivative * correction
            )
        )[0]
    )
    check_equal(
        "intrinsic level-7 second crossing scalar",
        gamma_seven,
        -700700,
    )

    labels = ((2, 1), (1, 3), (1, 5), (4, 1))
    expected_constants = (
        sp.Rational(9, 28),
        -sp.Rational(8, 105),
        -sp.Rational(1, 102375),
        sp.Rational(3, 61600),
    )
    for label, expected in zip(labels, expected_constants):
        check_equal(
            f"A_{label[0]}{label[1]}",
            residue_constant(*label).subs(b, b0),
            expected,
        )
        check_equal(
            f"fusion polynomial {label}",
            fusion_polynomial(*label).subs(b, b0),
            {
                (2, 1): expected_e_two,
                (1, 3): expected_e_three,
                (1, 5): expected_e_five,
                (4, 1): expected_e_four,
            }[label],
        )

    derivative = lambda expression: sp.diff(expression, b).subs(b, b0)
    h21, h13, h15, h41 = (kac_weight(*label) for label in labels)
    left_slope = sp.factor(
        (derivative(h21) - derivative(h13))
        / (derivative(h21) - derivative(h15))
    )
    right_slope = sp.factor(
        (derivative(h13) - derivative(h21))
        / (derivative(h13) - derivative(h41))
    )
    check_equal("energy left confluence slope", left_slope, sp.Rational(5, 11))
    check_equal(
        "energy right confluence slope",
        right_slope,
        sp.Rational(5, 13),
    )
    check_equal(
        "energy left nested residue",
        left_slope * expected_constants[0] * expected_constants[2],
        1 / gamma_seven,
    )
    check_equal(
        "energy right nested residue",
        right_slope * expected_constants[1] * expected_constants[3],
        1 / gamma_seven,
    )


if __name__ == "__main__":
    main()
