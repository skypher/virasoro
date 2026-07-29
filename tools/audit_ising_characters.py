#!/usr/bin/env python3
"""Exact replay of the three eta-reduced Ising quotient characters.

The BGG (Rocha-Caridi) numerators are expanded through grade 30 and the
resulting graded dimensions of L(1/2,h) are compared against an
independent free-fermion computation: the spin module is counted by
partitions into distinct positive integers, and the vacuum and energy
modules by partitions of 2N (respectively 2N+1) into distinct odd parts
with an even (respectively odd) number of parts.
"""

from collections import defaultdict

from sympy.functions.combinatorial.numbers import partition


MAXIMUM = 30

CASES = {
    "vacuum": (1, 7, "NS-even"),
    "energy": (5, 11, "NS-odd"),
    "spin": (-2, 10, "R"),
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


def bgg_dimensions(m, m_prime, maximum):
    eta_reduced = numerator(m, m_prime, maximum)
    return [
        sum(
            coefficient * int(partition(grade - exponent))
            for exponent, coefficient in eta_reduced.items()
            if exponent <= grade
        )
        for grade in range(maximum + 1)
    ]


def fermion_dimensions(sector, maximum):
    if sector == "R":
        # partitions into distinct positive integers
        table = [0] * (maximum + 1)
        table[0] = 1
        for part in range(1, maximum + 1):
            for total in range(maximum, part - 1, -1):
                table[total] += table[total - part]
        return table
    # NS sector: doubled grading, distinct odd parts, fermion parity
    doubled = 2 * maximum + 1
    table = [[0, 0] for _ in range(doubled + 1)]
    table[0][0] = 1
    for part in range(1, doubled + 1, 2):
        for total in range(doubled, part - 1, -1):
            table[total][0] += table[total - part][1]
            table[total][1] += table[total - part][0]
    if sector == "NS-even":
        return [table[2 * grade][0] for grade in range(maximum + 1)]
    return [table[2 * grade + 1][1] for grade in range(maximum + 1)]


def main():
    for name, (m, m_prime, sector) in CASES.items():
        bgg = bgg_dimensions(m, m_prime, MAXIMUM)
        fermionic = fermion_dimensions(sector, MAXIMUM)
        if bgg != fermionic:
            raise AssertionError(
                f"{name}: BGG dimensions {bgg} != fermionic {fermionic}"
            )
        print(
            f"PASS {name} Ising character through grade {MAXIMUM} "
            "(BGG vs free fermion)",
            flush=True,
        )


if __name__ == "__main__":
    main()
