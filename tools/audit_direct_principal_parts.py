#!/usr/bin/env python3
"""Direct verification of the principal-part theorems through level seven.

Unlike the confluence replays, this script tests the paper's closed
formulas against the inverse-Shapovalov definition itself: it
reconstructs H_N (N <= 7) exactly as rational functions of the internal
weight at sample external weights and compares Laurent data at the
collision points.  Verified here:

  * displayed Gram determinants and matrices (levels 2, 3, 4);
  * the singular vectors, crossing scalars, embedding diamond, and the
    intrinsic second crossing scalar gamma_7 = -700700;
  * Theorem "First fixed-c recursive residue" (level 3);
  * Theorem "Spin-sector fixed-c recursive principal part" (level 4),
    including the explicit degree-8 polynomial;
  * Proposition "No earlier nontransverse pole" (pole orders, N <= 6);
  * Theorem "First nontransverse fixed-c principal part" (level 7),
    both Laurent coefficients, with the explicit Theta_7 polynomial;
  * the level <= 4 collision-moment table of the paper;
  * closed forms of the finite parts Q_4^E and Q_5^E.
"""

import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from direct_reconstruction import (
    PONE,
    PH,
    RationalFunction,
    act,
    basis,
    euler_coeffs,
    gram_matrix,
    mat_eval,
    normal_order,
    padd,
    peval,
    pmul,
    pnorm,
    pscale,
    reconstruct_F,
    set_external_weight,
    vertex_matrix,
)

FAILURES = []


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAILURES.append(name)


def poly_det(matrix):
    if len(matrix) == 1:
        return matrix[0][0]
    det = ()
    for j in range(len(matrix)):
        minor = [row[:j] + row[j + 1:] for row in matrix[1:]]
        term = pmul(matrix[0][j], poly_det(minor))
        det = padd(det, term if j % 2 == 0 else pscale(term, -1))
    return det


def pderiv(poly):
    return pnorm(tuple(poly[i] * i for i in range(1, len(poly))))


def qform(matrix, left, right, hval=None, deriv=0):
    total = ()
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            total = padd(total, pscale(matrix[i][j], a * b))
    for _ in range(deriv):
        total = pderiv(total)
    return total if hval is None else peval(total, hval)


def apply_vector(level, coeffs, hval):
    for mode in range(1, level + 1):
        out = {}
        for coef, part in zip(coeffs, basis(level)):
            word = tuple(-y for y in part)
            for word2, poly in act(mode, word).items():
                out[word2] = out.get(word2, Fr(0)) + coef * peval(poly, hval)
        if any(value != 0 for value in out.values()):
            return False
    return True


def compose(parent_coeffs, parent_level, child_coeffs, child_level):
    total = {}
    for pcoef, ppart in zip(parent_coeffs, basis(parent_level)):
        pword = tuple(-y for y in ppart)
        for ccoef, cpart in zip(child_coeffs, basis(child_level)):
            cword = tuple(-z for z in cpart)
            for word, coef in normal_order(cword + pword).items():
                total[word] = total.get(word, Fr(0)) + pcoef * ccoef * coef
    return {w: c for w, c in total.items() if c != 0}


def matvec(matrix, vector):
    return [sum(row[j] * vector[j] for j in range(len(vector)))
            for row in matrix]


def rank_and_solve(matrix, rhs):
    n = len(matrix)
    aug = [matrix[i][:] + [rhs[i]] for i in range(n)]
    pivot_columns = []
    rank = 0
    for column in range(n):
        pivot = next((i for i in range(rank, n) if aug[i][column] != 0), None)
        if pivot is None:
            continue
        aug[rank], aug[pivot] = aug[pivot], aug[rank]
        aug[rank] = [x / aug[rank][column] for x in aug[rank]]
        for i in range(n):
            if i != rank and aug[i][column] != 0:
                factor = aug[i][column]
                aug[i] = [x - factor * y for x, y in zip(aug[i], aug[rank])]
        pivot_columns.append(column)
        rank += 1
    for i in range(rank, n):
        if aug[i][n] != 0:
            return rank, None
    solution = [Fr(0)] * n
    for i, column in enumerate(pivot_columns):
        solution[column] = aug[i][n]
    return rank, solution


LAMBDA = {n: Fr(n * n - 1, 48) for n in range(0, 16)}

XI2 = [Fr(-4, 3), Fr(1)]
XI3 = [Fr(3, 4), Fr(-3), Fr(1)]
CHI2 = [Fr(-3, 4), Fr(1)]
CHI4 = [Fr(-1, 4), Fr(11, 6), Fr(49, 144), Fr(-25, 6), Fr(1)]
PHI5 = [Fr(45), Fr(-54), Fr(-45), Fr(99, 4), Fr(36), Fr(-15), Fr(1)]
PHI4 = [Fr(-152, 3), Fr(88, 3), Fr(16), Fr(-40, 3), Fr(1)]

# closed forms of the finite parts, ascending coefficients in d
Q4_CLOSED = [Fr(0), Fr(592, 385), Fr(-59911073, 10672200),
             Fr(333192931, 53361000), Fr(-567514793, 213444000),
             Fr(7215811, 13340250), Fr(-159743, 3049200),
             Fr(123601, 53361000), Fr(-5641, 213444000)]
Q5_CLOSED = [Fr(0), Fr(17, 7), Fr(-264558547, 188806800),
             Fr(-117518068601, 16992612000), Fr(821675131523, 84963060000),
             Fr(-4300241117, 899080000), Fr(63926645827, 56642040000),
             Fr(-3873371069, 28321020000), Fr(4008577, 449540000),
             Fr(-848879, 2614248000), Fr(1190339, 169926120000)]


def structural_checks():
    gram2, gram3, gram4 = gram_matrix(2), gram_matrix(3), gram_matrix(4)
    expected3 = pmul(pmul((Fr(0), Fr(0), Fr(12)),
                          pmul((-1, Fr(2)), (-1, Fr(2)))),
                     pmul((-5, Fr(3)), (-1, Fr(16))))
    check("det G_3 matches the paper", poly_det(gram3) == expected3)
    expected4 = pmul((Fr(0),) * 3 + (Fr(12),),
                     pmul(pmul((-7, Fr(2)),
                               pmul((-1, Fr(2)),
                                    pmul((-1, Fr(2)), (-1, Fr(2))))),
                          pmul((-5, Fr(3)),
                               pmul((-21, Fr(16)),
                                    pmul((-1, Fr(16)),
                                         pmul((-1, Fr(16)),
                                              (-1, Fr(16))))))))
    check("det G_4 matches the paper", poly_det(gram4) == expected4)
    check("G_2(1/2,33/16) matches the paper",
          mat_eval(gram2, Fr(33, 16))
          == [[Fr(17, 2), Fr(99, 8)], [Fr(99, 8), Fr(1353, 32)]])

    check("xi_2 singular", apply_vector(2, XI2, Fr(1, 2)))
    check("xi_3 singular", apply_vector(3, XI3, Fr(1, 2)))
    check("chi_2 singular", apply_vector(2, CHI2, Fr(1, 16)))
    check("chi_4 singular", apply_vector(4, CHI4, Fr(1, 16)))
    check("phi_5 singular", apply_vector(5, PHI5, Fr(5, 2)))
    check("phi_4 singular", apply_vector(4, PHI4, Fr(7, 2)))

    check("b_xi2 = 28/9", qform(gram2, XI2, XI2, Fr(1, 2), 1) == Fr(28, 9))
    check("b_xi3 = -105/8", qform(gram3, XI3, XI3, Fr(1, 2), 1) == Fr(-105, 8))
    check("b_chi2 = -7/4", qform(gram2, CHI2, CHI2, Fr(1, 16), 1) == Fr(-7, 4))

    left = compose(XI2, 2, PHI5, 5)
    right = compose(XI3, 3, PHI4, 4)
    check("level-7 diamond identity", left == right)
    basis7 = basis(7)
    xi7 = [left.get(tuple(-y for y in part), Fr(0)) for part in basis7]
    check("xi_7 unit L_{-1}^7 coefficient", xi7[basis7.index((1,) * 7)] == 1)
    check("xi_7 singular at level 7", apply_vector(7, xi7, Fr(1, 2)))

    gram7 = gram_matrix(7)
    g0 = mat_eval(gram7, Fr(1, 2))
    g1 = [[peval(pderiv(entry), Fr(1, 2)) for entry in row] for row in gram7]
    g2 = [[peval(pderiv(pderiv(entry)), Fr(1, 2)) / 2 for entry in row]
          for row in gram7]
    rank, _ = rank_and_solve(g0, [Fr(0)] * 15)
    check("rank G_7(1/2,1/2) = 4", rank == 4)
    _, correction = rank_and_solve(g0, [-x for x in matvec(g1, xi7)])
    check("first-order correction exists", correction is not None)
    gamma7 = (sum(a * b for a, b in zip(xi7, matvec(g2, xi7)))
              + sum(a * b for a, b in zip(xi7, matvec(g1, correction))))
    check("gamma_7 = -700700 (intrinsic)", gamma7 == Fr(-700700))


def laurent_checks(dval):
    print(f"-- external weight d = {dval}", flush=True)
    set_external_weight(dval)
    d = Fr(dval)
    coefficients = {0: RationalFunction((Fr(1),), (Fr(1),))}
    for level in range(1, 8):
        coefficients[level] = reconstruct_F(level, verbose=False)
    euler = euler_coeffs(7)

    def laurent_H(level, point, kmax=0):
        total = {}
        for j in range(level + 1):
            if euler[level - j] == 0:
                continue
            for k, value in coefficients[j].laurent_at(point, kmax).items():
                total[k] = total.get(k, Fr(0)) + euler[level - j] * value
        return {k: v for k, v in total.items() if v != 0 or k >= 0}

    def value_H(level, point):
        laurent = laurent_H(level, point)
        assert all(v == 0 for k, v in laurent.items() if k < 0)
        return laurent.get(0, Fr(0))

    e2 = d * (d - 1) * (3 * d - 14) * (3 * d - 5) / 9
    e3 = (d * (d - 1) * (2 * d - 15) * (2 * d - 7)
          * (2 * d - 5) * (2 * d - 1) / 16)
    e5 = (d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
          * (2 * d - 15) * (2 * d - 7) * (2 * d - 5) * (2 * d - 1) / 16)
    p2 = d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 4
    p4 = (d * (d - 1) * (2 * d - 7) * (2 * d - 1) * (3 * d - 14)
          * (3 * d - 5) * (6 * d - 55) * (6 * d - 1) / 1296)

    laurent3 = laurent_H(3, Fr(1, 2))
    check("level-3 residue theorem",
          laurent3.get(-1) == Fr(9, 28) * e2 * value_H(1, Fr(5, 2))
          - Fr(8, 105) * e3)

    laurent4 = laurent_H(4, Fr(1, 16))
    recursive = (Fr(-4, 7) * p2 * value_H(2, Fr(33, 16))
                 + Fr(648, 13475) * p4)
    explicit = (d * (d - 1) * (2 * d - 7) * (2 * d - 1)
                * (248 * d**4 - 5752 * d**3 + 25274 * d**2
                   - 33630 * d + 5775) / 40425)
    check("level-4 residue theorem (recursive form)",
          laurent4.get(-1) == recursive)
    check("level-4 residue theorem (explicit polynomial)",
          recursive == explicit)

    simple = True
    for level in range(1, 7):
        for n in LAMBDA:
            laurent = laurent_H(level, LAMBDA[n])
            worst = min([k for k in laurent if laurent[k] != 0], default=0)
            if worst < -1:
                simple = False
    check("no double pole through level 6", simple)

    # level <= 4 collision-moment table
    table = {
        (1, 1): d * (d - 1) / 2,
        (1, 2): d**2 * (d - 1)**2 / 4,
        (2, 2): -d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 7,
        (5, 2): d * (d - 1) * (3 * d - 14) * (3 * d - 5) / 28,
        (1, 3): d**2 * (d - 1)**2 * (17 * d**2 - 113 * d + 236) / 120,
        (2, 3): -8 * d**2 * (d - 1)**2 * (2 * d - 7) * (2 * d - 1) / 231,
        (5, 3): -d * (d - 1) * (d**4 - 50 * d**3 + 311 * d**2
                                - 550 * d + 210) / 84,
        (9, 3): 3 * d * (d - 11) * (d - 6) * (d - 1)
                * (3 * d - 14) * (3 * d - 5) / 3080,
        (1, 4): -d**2 * (d - 1)**2 * (31 * d**4 - 830 * d**3
                 + 5567 * d**2 - 13408 * d + 8460) / 1440,
        (2, 4): explicit,
        (5, 4): -d**2 * (d - 1)**2 * (149 * d**4 - 2506 * d**3
                 - 2679 * d**2 + 70508 * d - 106540) / 61152,
        (8, 4): -2 * d * (d - 13) * (d - 6) * (d - 1) * (2 * d - 15)
                * (2 * d - 7) * (2 * d - 5) * (2 * d - 1) / 20475,
        (9, 4): 9 * d**2 * (d - 11) * (d - 6) * (d - 1)**2
                * (3 * d - 14) * (3 * d - 5) / 86240,
        (13, 4): d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
                 * (3 * d - 14) * (3 * d - 5) / 184800,
    }
    table_ok = True
    for level in range(1, 5):
        for n in LAMBDA:
            laurent = laurent_H(level, LAMBDA[n])
            residue = laurent.get(-1, Fr(0))
            if residue != table.get((n, level), Fr(0)):
                table_ok = False
    check("level <= 4 collision-moment table", table_ok)

    # level 7: complete principal part with explicit Theta_7
    theta7 = (-(d**2 * (d - 1)**2 * (2 * d - 15) * (2 * d - 7)
                * (2 * d - 5) * (2 * d - 1) * (3 * d - 14) * (3 * d - 5))
              * (84001 * d**4 - 3376370 * d**3 + 44478887 * d**2
                 - 209562838 * d + 205096320) / Fr(2164322160000))
    laurent5 = laurent_H(5, Fr(5, 2))
    laurent4b = laurent_H(4, Fr(7, 2))
    check("H_5 simple pole at 5/2", min(laurent5) == -1)
    check("H_4 simple pole at 7/2", min(laurent4b) == -1)
    q5 = laurent5.get(0, Fr(0))
    q4 = laurent4b.get(0, Fr(0))
    check("closed form of Q_4^E", peval(pnorm(tuple(Q4_CLOSED)), d) == q4)
    check("closed form of Q_5^E", peval(pnorm(tuple(Q5_CLOSED)), d) == q5)

    laurent7 = laurent_H(7, Fr(1, 2))
    check("level-7 double-pole coefficient",
          laurent7.get(-2) == -e2 * e5 / 700700)
    check("level-7 simple-pole coefficient (with explicit Theta_7)",
          laurent7.get(-1)
          == Fr(9, 28) * e2 * q5 - Fr(8, 105) * e3 * q4 + theta7)
    check("level-7 pole order exactly 2",
          min(laurent7) == -2 and laurent7[-2] != 0)


def main():
    start = time.time()
    structural_checks()
    for dval in (Fr(3, 7), Fr(23)):
        laurent_checks(dval)
    print(f"total {time.time() - start:.0f}s", flush=True)
    if FAILURES:
        raise AssertionError(f"failed checks: {FAILURES}")


if __name__ == "__main__":
    main()
