#!/usr/bin/env python3
"""Exact low-level torus Virasoro blocks from Shapovalov matrices.

The program works at fixed central charge and keeps the internal and external
weights symbolic.  It is intended for exact exploration of the first Ising
resonances, not for large numerical sweeps.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from functools import lru_cache

import sympy as sp


h, d, c, z = sp.symbols("h d c z")


def partitions(n: int, largest: int | None = None):
    """Partitions of n as tuples in weakly decreasing order."""
    if n == 0:
        yield ()
        return
    if largest is None or largest > n:
        largest = n
    for first in range(largest, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def _add_term(target, word, coefficient):
    coefficient = sp.expand(coefficient)
    if coefficient != 0:
        target[word] += coefficient


@lru_cache(maxsize=None)
def normal_order_negative(word: tuple[int, ...]):
    """PBW-normal-order a word of strictly negative Virasoro modes."""
    if any(mode >= 0 for mode in word):
        raise ValueError(f"expected negative modes, got {word}")
    for index in range(len(word) - 1):
        left, right = word[index], word[index + 1]
        if left > right:
            result = defaultdict(lambda: sp.Integer(0))
            swapped = word[:index] + (right, left) + word[index + 2 :]
            for new_word, coefficient in normal_order_negative(swapped).items():
                _add_term(result, new_word, coefficient)
            bracketed = word[:index] + (left + right,) + word[index + 2 :]
            for new_word, coefficient in normal_order_negative(bracketed).items():
                _add_term(result, new_word, (left - right) * coefficient)
            return dict(result)
    return {word: sp.Integer(1)}


@lru_cache(maxsize=None)
def act_mode(mode: int, word: tuple[int, ...]):
    """Act with L_mode on a PBW word applied to a highest-weight vector."""
    if mode < 0:
        return normal_order_negative((mode,) + word)
    if mode == 0:
        level = -sum(word)
        return {word: h + level}
    if not word:
        return {}

    first, rest = word[0], word[1:]
    result = defaultdict(lambda: sp.Integer(0))

    # L_mode L_first = L_first L_mode + [L_mode,L_first].
    for acted_word, coefficient in act_mode(mode, rest).items():
        for new_word, normal_coefficient in normal_order_negative(
            (first,) + acted_word
        ).items():
            _add_term(result, new_word, coefficient * normal_coefficient)

    for acted_word, coefficient in act_mode(mode + first, rest).items():
        _add_term(result, acted_word, (mode - first) * coefficient)

    if mode + first == 0:
        central = c * (mode**3 - mode) / 12
        _add_term(result, rest, central)

    return dict(result)


def act_on_combination(mode: int, combination):
    result = defaultdict(lambda: sp.Integer(0))
    for word, outer_coefficient in combination.items():
        for new_word, inner_coefficient in act_mode(mode, word).items():
            _add_term(result, new_word, outer_coefficient * inner_coefficient)
    return dict(result)


def gram_entry(left_partition, right_partition):
    combination = {
        tuple(-part for part in right_partition): sp.Integer(1),
    }
    # The rightmost operator in the adjoint word acts first.
    for mode in left_partition:
        combination = act_on_combination(mode, combination)
    return sp.expand(combination.get((), 0))


def ward(mode: int, expression):
    """Action of [L_mode,V_d(z)] on a matrix element."""
    return sp.expand(
        z**mode * (z * sp.diff(expression, z) + (mode + 1) * d * expression)
    )


@lru_cache(maxsize=None)
def vertex_entry_words(left_word: tuple[int, ...], right_word: tuple[int, ...]):
    """Compute <h|left_word V_d(z) right_word|h> exactly."""
    if left_word:
        nearest = left_word[-1]
        shortened = left_word[:-1]
        result = ward(nearest, vertex_entry_words(shortened, right_word))
        for new_word, coefficient in act_mode(nearest, right_word).items():
            result += coefficient * vertex_entry_words(shortened, new_word)
        return sp.expand(result)

    if right_word:
        nearest = right_word[0]
        shortened = right_word[1:]
        return sp.expand(-ward(nearest, vertex_entry_words((), shortened)))

    return z ** (-d)


def vertex_entry(left_partition, right_partition):
    left_word = tuple(reversed(left_partition))
    right_word = tuple(-part for part in right_partition)
    return sp.expand(vertex_entry_words(left_word, right_word).subs(z, 1))


def level_matrices(level: int, central_charge=sp.Rational(1, 2)):
    basis = list(partitions(level))
    gram = sp.Matrix(
        [
            [gram_entry(left, right).subs(c, central_charge) for right in basis]
            for left in basis
        ]
    )
    vertex = sp.Matrix(
        [
            [
                vertex_entry(left, right).subs(c, central_charge)
                for right in basis
            ]
            for left in basis
        ]
    )
    return basis, gram, vertex


def torus_coefficient(level: int, central_charge=sp.Rational(1, 2)):
    if level == 0:
        return sp.Integer(1)
    _, gram, vertex = level_matrices(level, central_charge)
    # Sum (G^{-1})_{ij} rho_{ij} = tr(G^{-1} rho^T).
    solved = gram.inv(method="GE") * vertex.T
    return sp.factor(sp.cancel(sp.trace(solved)))


def euler_coefficients(max_level: int):
    coefficients = [sp.Integer(1)] + [sp.Integer(0)] * max_level
    for mode in range(1, max_level + 1):
        for degree in range(max_level, mode - 1, -1):
            coefficients[degree] -= coefficients[degree - mode]
    return coefficients


def h_coefficients(max_level: int, central_charge=sp.Rational(1, 2)):
    f_coefficients = []
    for level in range(max_level + 1):
        print(f"computing exact coefficient at level {level}", flush=True)
        f_coefficients.append(torus_coefficient(level, central_charge))
    euler = euler_coefficients(max_level)
    result = []
    for level in range(max_level + 1):
        coefficient = sum(
            euler[offset] * f_coefficients[level - offset]
            for offset in range(level + 1)
        )
        result.append(sp.factor(sp.cancel(coefficient)))
    return f_coefficients, result


def pole_order(expression, point):
    numerator, denominator = sp.fraction(sp.cancel(expression))

    def valuation(polynomial):
        polynomial = sp.Poly(polynomial, h, domain="EX")
        factor = sp.Poly(h - point, h, domain="EX")
        order = 0
        while not polynomial.is_zero and polynomial.eval(point) == 0:
            polynomial, remainder = sp.div(polynomial, factor)
            if not remainder.is_zero:
                raise ArithmeticError("failed exact polynomial division")
            order += 1
        return order

    denominator_order = valuation(denominator)
    numerator_order = valuation(numerator)
    return max(0, denominator_order - numerator_order)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-level", type=int, default=2)
    args = parser.parse_args()
    if not 0 <= args.max_level <= 3:
        parser.error(
            "the symbolic Python path is restricted to levels 0..3; "
            "higher coefficient generation must use the parallel C++ path"
        )

    f_coefficients, reduced_coefficients = h_coefficients(args.max_level)
    euler = euler_coefficients(args.max_level)

    print(f"fixed central charge c = 1/2; levels 0..{args.max_level}", flush=True)
    print(f"Euler coefficients: {euler}", flush=True)
    for level in range(args.max_level + 1):
        _, gram, _ = level_matrices(level) if level else ((), sp.eye(1), sp.eye(1))
        determinant = sp.factor(gram.det())
        identity_check = sp.simplify(
            f_coefficients[level].subs(d, 0) - len(list(partitions(level)))
        )
        if identity_check != 0:
            raise AssertionError(
                f"identity insertion failed at level {level}: {identity_check}"
            )
        print(f"level {level}: det G = {determinant}", flush=True)
        print(f"level {level}: F = {f_coefficients[level]}", flush=True)
        print(f"level {level}: H = {reduced_coefficients[level]}", flush=True)
        for index in range(0, 13):
            point = sp.Rational(index * index - 1, 48)
            order = pole_order(reduced_coefficients[level], point)
            if order:
                print(
                    f"  pole lambda_{index}={point}: order {order}",
                    flush=True,
                )


if __name__ == "__main__":
    main()
