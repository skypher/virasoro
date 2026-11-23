#!/usr/bin/env python3
"""Exact regularity minors at the Ising weights (cross-check of Lemma
lem:regular-everywhere).

Usage: python3 -u tools/audit_regular_families.py [-h|--help]

For each displayed Kac label (r,s) with m = rs and Ising weight h, the
matrix S_m(1/2,h) of v -> (L_1 v, L_2 v) on the level-m PBW space is built
by exact Virasoro commutation, with partitions in decreasing lexicographic
order and L_1-rows before L_2-rows.  B_m consists of its first p(m)-1 rows
followed by the coordinate row of L_{-1}^m.  Each determinant is compared
with the value stored in CASES; a nonzero determinant makes the normalized
singular-vector family regular at b_0 by Cramer's rule.
"""

import argparse
import sys

import sympy as sp

import exact_shapovalov as es


R = sp.Rational

CASES = [
    ((2, 1), R(1, 2), R(3)),
    ((1, 3), R(1, 2), R(12)),
    ((1, 2), R(1, 16), R(3)),
    ((2, 2), R(1, 16), R(-675, 2)),
    ((1, 5), R(5, 2), R(91350)),
    ((4, 1), R(7, 2), R(-2730)),
    ((4, 2), R(33, 16), R(-17116376343198212705625, 32)),
    ((1, 6), R(65, 16), R(505194765075, 32)),
]


def raising_matrix(level, weight):
    columns = list(es.partitions(level))
    words = [tuple(-part for part in partition) for partition in columns]
    rows = []
    for mode in (1, 2):
        target = list(es.partitions(level - mode))
        index = {tuple(-part for part in p): i for i, p in enumerate(target)}
        block = [[sp.Integer(0)] * len(columns) for _ in target]
        for column, word in enumerate(words):
            for new_word, coefficient in es.act_mode(mode, word).items():
                block[index[new_word]][column] += sp.expand(coefficient).subs(
                    {es.c: R(1, 2), es.h: weight}
                )
        rows.extend(block)
    return columns, rows


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    failures = 0
    for (r, s), weight, expected in CASES:
        level = r * s
        columns, rows = raising_matrix(level, weight)
        last = [
            sp.Integer(1) if p == (1,) * level else sp.Integer(0) for p in columns
        ]
        matrix = sp.Matrix(rows[: len(columns) - 1] + [last])
        value = sp.nsimplify(matrix.det())
        if value == expected and value != 0:
            print(f"PASS label ({r},{s}) level {level} h={weight}: det B = {value}")
        else:
            failures += 1
            print(
                f"FAIL label ({r},{s}) level {level} h={weight}: "
                f"det B = {value}, expected {expected}"
            )
    if failures:
        sys.exit(1)


if __name__ == "__main__":
    main()
