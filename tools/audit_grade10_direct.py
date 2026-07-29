#!/usr/bin/env python3
"""Direct 42x42 verification of the grade-ten principal-part theorem.

This is the slow, definition-side audit (roughly ten minutes): it
reconstructs H_N (N <= 10) exactly as rational functions of the internal
weight at a sample external weight, directly from the inverse-Shapovalov
definition, and verifies:

  * dim ker G_10(1/2, 1/16) = 32 and the determinant valuation 33
    (Proposition "Grade-ten Smith profile");
  * the residues of H_8 at 33/16 and H_6 at 65/16 against the generic
    residue constants (equation (6.1) normalization at levels 8 and 6);
  * the closed forms of the finite parts Q_8 and Q_6;
  * both Laurent coefficients of H_10 at 1/16, i.e. the complete
    principal part of Theorem "Finite recursive grade-ten principal
    part", including the value gamma_10 = -1121229484375/192 and the
    explicit polynomial Theta_10;
  * pole orders of H_7..H_10 at every lambda_n, n < 24 (double poles
    occur exactly in the energy class for N >= 7 and in the spin class
    at N = 10).

Run separately from the default audit:  make audit-deep.
"""

import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from direct_reconstruction import (
    RationalFunction,
    basis,
    euler_coeffs,
    gram_matrix,
    mat_eval,
    peval,
    pnorm,
    reconstruct_F,
    set_external_weight,
)

FAILURES = []


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAILURES.append(name)


LAMBDA = {n: Fr(n * n - 1, 48) for n in range(0, 24)}
DVAL = Fr(3, 7)

# closed forms of the finite parts, ascending coefficients in d
Q6_CLOSED = [
    Fr(0), Fr(233, 182), Fr(644839496663777, 515816086786000),
    Fr(-4403093657926279, 384572940444000),
    Fr(228862730727857308591, 14623386060383100000),
    Fr(-662146631382819574841, 73116930301915500000),
    Fr(202297853959208151979, 73116930301915500000),
    Fr(-392346747350033647, 794749242412125000),
    Fr(18368952184880657, 332349683190525000),
    Fr(-338539304863589, 83087420797631250),
    Fr(27741573920257, 138479034662718750),
    Fr(-4598471246794, 761634690644953125),
    Fr(8383184974, 99343655301515625),
]
Q8_CLOSED = [
    Fr(0), Fr(4168, 8645), Fr(-296209014191879717, 2785406868644400),
    Fr(189065206495901633, 386862065089500),
    Fr(-117514755236816996017207, 122836442907218040000),
    Fr(17781878180052216443429, 17060617070446950000),
    Fr(-3237317718005660383833727, 4606366609020676500000),
    Fr(325304314990330120281847, 1046901502050153750000),
    Fr(-130036594457234730335197, 1395868669400205000000),
    Fr(1261471967028889835486, 65431343878134609375),
    Fr(-32552440798124902027, 11750935227093562500),
    Fr(5068074419635309294, 18454994427166171875),
    Fr(-2030808625721293963, 110729966562997031250),
    Fr(561770543735461264, 719744782659480703125),
    Fr(-4461402226295372, 239914927553160234375),
    Fr(90772688, 562245704645625),
    Fr(748860211724, 719744782659480703125),
]


def kernel_dimension(matrix):
    n = len(matrix)
    rows = [row[:] for row in matrix]
    rank = 0
    for column in range(n):
        pivot = next((i for i in range(rank, n) if rows[i][column] != 0),
                     None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        rows[rank] = [x / rows[rank][column] for x in rows[rank]]
        for i in range(n):
            if i != rank and rows[i][column] != 0:
                factor = rows[i][column]
                rows[i] = [x - factor * y
                           for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return n - rank


def poly_valuation(poly, point):
    value = 0
    current = list(poly)
    while current and peval(pnorm(tuple(current)), point) == 0:
        quotient = [Fr(0)] * (len(current) - 1)
        acc = current[-1]
        for i in range(len(current) - 2, -1, -1):
            quotient[i] = acc
            acc = current[i] + acc * point
        assert acc == 0
        current = list(pnorm(tuple(quotient)))
        value += 1
    return value


def main():
    start = time.time()
    d = DVAL
    set_external_weight(d)

    coefficients = {0: RationalFunction((Fr(1),), (Fr(1),))}
    for level in range(1, 11):
        coefficients[level] = reconstruct_F(level)
        print(f"reconstructed F_{level} ({time.time() - start:.0f}s)",
              flush=True)
    euler = euler_coeffs(10)

    def laurent_H(level, point, kmax=0):
        total = {}
        for j in range(level + 1):
            if euler[level - j] == 0:
                continue
            for k, value in coefficients[j].laurent_at(point, kmax).items():
                total[k] = total.get(k, Fr(0)) + euler[level - j] * value
        return {k: v for k, v in total.items() if v != 0 or k >= 0}

    gram10 = gram_matrix(10)
    check("dim ker G_10(1/2,1/16) = 32",
          kernel_dimension(mat_eval(gram10, Fr(1, 16))) == 32)
    check("ord det G_10 at 1/16 = 33",
          poly_valuation(coefficients[10].den, Fr(1, 16)) == 33)

    p2 = d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 4
    p4 = (d * (d - 1) * (2 * d - 7) * (2 * d - 1) * (3 * d - 14)
          * (3 * d - 5) * (6 * d - 55) * (6 * d - 1) / 1296)
    p42 = (d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
           * (2 * d - 57) * (2 * d - 35) * (2 * d - 15) * (2 * d - 7)
           * (2 * d - 5) * (2 * d - 1) * (3 * d - 14) * (3 * d - 5)
           * (6 * d - 55) * (6 * d - 1) / 20736)
    p16 = (d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
           * (2 * d - 57) * (2 * d - 35) * (2 * d - 15) * (2 * d - 7)
           * (2 * d - 5) * (2 * d - 1) / 64)
    check("fusion factorization P_2 P_42 = P_4 P_16", p2 * p42 == p4 * p16)

    theta10 = (-(d**2 * (d - 1)**2 * (2 * d - 7)**2 * (2 * d - 1)**2
                 * (3 * d - 14) * (3 * d - 5) * (6 * d - 55) * (6 * d - 1))
               * (424640464 * d**8 - 41506307104 * d**7
                  + 1664502727528 * d**6 - 35552058801520 * d**5
                  + 438148123547677 * d**4 - 3142854705332170 * d**3
                  + 12488401942129875 * d**2 - 23870935242348750 * d
                  + 14566042731240000) / Fr(552735279561465000000))

    laurent8 = laurent_H(8, Fr(33, 16))
    laurent6 = laurent_H(6, Fr(65, 16))
    check("H_8 simple pole at 33/16", min(laurent8) == -1)
    check("H_6 simple pole at 65/16", min(laurent6) == -1)
    check("Res H_8 at 33/16 = A_42 P_42",
          laurent8[-1] == Fr(48, 32035128125) * p42)
    check("Res H_6 at 65/16 = A_16 P_16",
          laurent6[-1] == Fr(-8, 320945625) * p16)
    check("closed form of Q_8",
          peval(pnorm(tuple(Q8_CLOSED)), d) == laurent8.get(0, Fr(0)))
    check("closed form of Q_6",
          peval(pnorm(tuple(Q6_CLOSED)), d) == laurent6.get(0, Fr(0)))

    laurent10 = laurent_H(10, Fr(1, 16))
    check("grade-10 double-pole coefficient (gamma_10)",
          laurent10.get(-2) == Fr(-192, 1121229484375) * p2 * p42)
    predicted = (Fr(-4, 7) * p2 * laurent8.get(0, Fr(0))
                 + Fr(648, 13475) * p4 * laurent6.get(0, Fr(0)) + theta10)
    check("grade-10 simple-pole coefficient (with explicit Theta_10)",
          laurent10.get(-1) == predicted)
    check("grade-10 pole order exactly 2",
          min(laurent10) == -2 and laurent10[-2] != 0)

    # pole orders of H_7..H_10 everywhere: double poles exactly in the
    # energy class (N >= 7) and the spin class at N = 10
    expected_doubles = {(7, 5), (8, 5), (9, 5), (10, 5), (10, 2)}
    found = set()
    excess = []
    for level in range(7, 11):
        for n in LAMBDA:
            laurent = laurent_H(level, LAMBDA[n])
            worst = -min([k for k in laurent if laurent[k] != 0], default=0)
            if worst == 2:
                found.add((level, n))
            elif worst > 2:
                excess.append((level, n, worst))
    check("double poles occur exactly where predicted",
          found == expected_doubles and not excess)

    print(f"total {time.time() - start:.0f}s", flush=True)
    if FAILURES:
        raise AssertionError(f"failed checks: {FAILURES}")


if __name__ == "__main__":
    main()
