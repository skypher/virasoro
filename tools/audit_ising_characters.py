#!/usr/bin/env python3
"""Exact replay of the three eta-reduced Ising quotient characters."""

from collections import defaultdict

from sympy.functions.combinatorial.numbers import partition


CASES = {
    "vacuum": (
        1,
        7,
        [1, 0, 1, 1, 2, 2, 3, 3, 5, 5, 7, 8, 11, 12, 16, 18],
    ),
    "energy": (
        5,
        11,
        [1, 1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 12, 14, 17, 20],
    ),
    "spin": (
        -2,
        10,
        [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27],
    ),
}


def numerator(m, m_prime, maximum):
    result = defaultdict(int)
    for j in range(-maximum, maximum + 1):
        first = ((24 * j + m) ** 2 - m**2) // 48
        second = ((24 * j + m_prime) ** 2 - m**2) // 48
        if 0 <= first <= maximum:
            result[first] += 1
        if 0 <= second <= maximum:
            result[second] -= 1
    return result


def main():
    maximum = 15
    for name, (m, m_prime, expected) in CASES.items():
        eta_reduced = numerator(m, m_prime, maximum)
        dimensions = [
            sum(
                coefficient * int(partition(grade - exponent))
                for exponent, coefficient in eta_reduced.items()
                if exponent <= grade
            )
            for grade in range(maximum + 1)
        ]
        if dimensions != expected:
            raise AssertionError(
                f"{name}: dimensions {dimensions}, expected {expected}"
            )
        print(f"PASS {name} Ising character through grade {maximum}", flush=True)


if __name__ == "__main__":
    main()
