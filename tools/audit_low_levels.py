#!/usr/bin/env python3
"""Independent exact assertions for the low-level Ising calculations."""

import sympy as sp

from exact_shapovalov import (
    act_mode,
    c,
    d,
    h,
    h_coefficients,
    level_matrices,
    partitions,
)


def check_equal(name, actual, expected):
    difference = sp.factor(sp.cancel(actual - expected))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    print(f"PASS {name}", flush=True)


def check_singular(name, level, basis, vector, central_charge, weight):
    for positive_mode in range(1, level + 1):
        coefficients = {}
        for scalar, partition in zip(vector, basis):
            word = tuple(-part for part in partition)
            for output_word, output_scalar in act_mode(
                positive_mode, word
            ).items():
                coefficients[output_word] = (
                    coefficients.get(output_word, 0)
                    + scalar
                    * output_scalar.subs({c: central_charge, h: weight})
                )
        for coefficient in coefficients.values():
            if sp.factor(coefficient) != 0:
                raise AssertionError(
                    f"{name}: L_{positive_mode} gives {coefficient}"
                )
    print(f"PASS {name}", flush=True)


def main():
    _, gram_one, _ = level_matrices(1)
    check_equal("level-1 Gram determinant", gram_one.det(), 2 * h)

    _, gram_two, _ = level_matrices(2)
    check_equal(
        "level-2 Gram determinant",
        sp.factor(gram_two.det()),
        h * (2 * h - 1) * (16 * h - 1),
    )

    _, reduced = h_coefficients(2)
    expected_one = d * (d - 1) / (2 * h)
    check_equal("level-1 reduced coefficient", reduced[1], expected_one)

    expected_two = (
        d
        * (d - 1)
        * (
            16 * d**2 * h
            + d**2
            - 112 * d * h
            - d
            + 192 * h**2
            + 44 * h
        )
        / (4 * h * (2 * h - 1) * (16 * h - 1))
    )
    check_equal("level-2 reduced coefficient", reduced[2], expected_two)

    basis_four, gram_four, _ = level_matrices(4)
    expected_det_four = (
        12
        * h**3
        * (2 * h - 7)
        * (2 * h - 1) ** 3
        * (3 * h - 5)
        * (16 * h - 21)
        * (16 * h - 1) ** 3
    )
    check_equal(
        "level-4 Gram determinant",
        sp.factor(gram_four.det()),
        expected_det_four,
    )

    collision = sp.Rational(1, 16)
    specialized = gram_four.subs(h, collision)
    if specialized.rank() != 2:
        raise AssertionError(
            f"level-4 rank at 1/16 is {specialized.rank()}, expected 2"
        )
    print("PASS level-4 rank at 1/16", flush=True)

    expected_basis = [(4,), (3, 1), (2, 2), (2, 1, 1), (1, 1, 1, 1)]
    if basis_four != expected_basis:
        raise AssertionError(f"unexpected level-4 basis {basis_four}")
    print("PASS level-4 PBW basis order", flush=True)

    null_vectors = [
        sp.Matrix([sp.Rational(-9, 16), sp.Rational(-3, 2), 1, 0, 0]),
        sp.Matrix([sp.Rational(-27, 64), sp.Rational(-9, 8), 0, 1, 0]),
        sp.Matrix(
            [sp.Rational(-465, 256), sp.Rational(-75, 32), 0, 0, 1]
        ),
    ]
    for index, vector in enumerate(null_vectors, start=1):
        if specialized * vector != sp.zeros(5, 1):
            raise AssertionError(f"level-4 null vector {index} failed")
    print("PASS three level-4 null vectors at 1/16", flush=True)

    central_charge = sp.Rational(1, 2)
    collision = sp.Rational(1, 16)
    basis_two = list(partitions(2))
    chi_two = sp.Matrix([sp.Rational(-3, 4), 1])
    basis_three, gram_three, vertex_three = level_matrices(3)
    expected_basis_three = [(3,), (2, 1), (1, 1, 1)]
    if basis_three != expected_basis_three:
        raise AssertionError(f"unexpected level-3 basis {basis_three}")
    descendant_three = sp.Matrix(
        [sp.Rational(-3, 4), sp.Rational(-3, 4), 1]
    )
    chi_four = sp.Matrix(
        [
            sp.Rational(-1, 4),
            sp.Rational(11, 6),
            sp.Rational(49, 144),
            sp.Rational(-25, 6),
            1,
        ]
    )
    check_singular(
        "level-2 singular vector",
        2,
        basis_two,
        chi_two,
        central_charge,
        collision,
    )
    check_singular(
        "level-4 singular vector",
        4,
        basis_four,
        chi_four,
        central_charge,
        collision,
    )

    shifted_weight = collision + 2
    crossing_two = sp.factor(
        (chi_two.T * gram_two.diff(h).subs(h, collision) * chi_two)[0]
    )
    check_equal(
        "level-2 singular crossing scalar",
        crossing_two,
        sp.Rational(-7, 4),
    )
    crossing_three = sp.factor(
        (
            descendant_three.T
            * gram_three.diff(h).subs(h, collision)
            * descendant_three
        )[0]
    )
    expected_crossing_three = (
        sp.Rational(-7, 4) * 2 * shifted_weight
    )
    check_equal(
        "level-3 descendant crossing scalar",
        crossing_three,
        expected_crossing_three,
    )

    descendant_columns = sp.Matrix(
        [
            [0, sp.Rational(-3, 2)],
            [0, sp.Rational(-3, 2)],
            [sp.Rational(-3, 4), 0],
            [1, sp.Rational(-3, 4)],
            [0, 1],
        ]
    )
    kernel_basis = descendant_columns.row_join(chi_four)
    crossing = sp.factor(
        kernel_basis.T
        * gram_four.diff(h).subs(h, collision)
        * kernel_basis
    )
    expected_crossing = sp.diag(
        sp.Rational(-7, 4) * gram_two.subs(h, shifted_weight),
        sp.Rational(13475, 648),
    )
    if crossing != expected_crossing:
        raise AssertionError(
            f"spin-collision crossing form mismatch:\n{crossing}"
        )
    print("PASS spin-collision derivative crossing form", flush=True)

    _, _, vertex_two = level_matrices(2)
    _, _, vertex_four = level_matrices(4)
    fusion_two = sp.factor(
        (chi_two.T * vertex_two.subs(h, collision) * chi_two)[0]
    )
    expected_fusion_two = (
        d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 4
    )
    check_equal(
        "level-2 singular-vector torus polynomial",
        fusion_two,
        expected_fusion_two,
    )
    _, _, vertex_one = level_matrices(1)
    restricted_vertex_three = sp.factor(
        (
            descendant_three.T
            * vertex_three.subs(h, collision)
            * descendant_three
        )[0]
    )
    check_equal(
        "level-3 singular-submodule torus restriction",
        restricted_vertex_three,
        fusion_two * vertex_one.subs(h, shifted_weight)[0, 0],
    )

    fusion_four = sp.factor(
        (chi_four.T * vertex_four.subs(h, collision) * chi_four)[0]
    )
    expected_fusion_four = (
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
    check_equal(
        "level-4 singular-vector torus polynomial",
        fusion_four,
        expected_fusion_four,
    )

    inverse_crossing = crossing.inv()
    residue_inverse_four = sp.factor(
        kernel_basis * inverse_crossing * kernel_basis.T
    )
    residue_f_four = sp.factor(
        sp.trace(residue_inverse_four * vertex_four.subs(h, collision).T)
    )
    f_coefficients, reduced_coefficients = h_coefficients(2)
    residue_f_three = sp.factor(
        restricted_vertex_three / crossing_three
    )
    residue_f_two = sp.factor(sp.Rational(-4, 7) * fusion_two)
    check_equal(
        "fixed-c recursive residue at level 3",
        residue_f_three,
        sp.Rational(-4, 7)
        * fusion_two
        * f_coefficients[1].subs(h, shifted_weight),
    )
    residue_h_four = sp.factor(
        residue_f_four - residue_f_three - residue_f_two
    )
    recursive_residue = sp.factor(
        sp.Rational(-4, 7)
        * fusion_two
        * reduced_coefficients[2].subs(h, shifted_weight)
        + sp.Rational(648, 13475) * fusion_four
    )
    check_equal(
        "fixed-c recursive residue at level 4",
        residue_h_four,
        recursive_residue,
    )

    expected_residue = (
        d
        * (d - 1)
        * (2 * d - 7)
        * (2 * d - 1)
        * (
            248 * d**4
            - 5752 * d**3
            + 25274 * d**2
            - 33630 * d
            + 5775
        )
        / 40425
    )
    check_equal(
        "expanded level-4 residue polynomial",
        recursive_residue,
        expected_residue,
    )


if __name__ == "__main__":
    main()
