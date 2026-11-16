#!/usr/bin/env python3
"""Exact replay of Theorem thm:top-layer at the Ising charge through level ten.

Usage: python3 -u tools/audit_top_layer.py [-h|--help] [--max-level N] [--d D]

At c = 1/2 the three interior weights are lambda = 0, 1/2, 1/16, with
first-layer singular levels (1, 6), (2, 3), (2, 4) and second-layer levels
starting at 11, 7, 10.  For every level N <= max-level (default 10) the
script reconstructs H_N(1/2, Delta, d) exactly as a rational function of the
internal weight at the external weight d (default 3/7), directly from the
inverse-Shapovalov definition, and checks at each lambda:

  * the pole order of H_N equals the Jantzen depth j_N(lambda);
  * the leading Laurent coefficient equals
        sum_sigma tau_sigma(d) / gamma_sigma * H_{N - l_sigma}(1/2, lambda + l_sigma, d).

For the first layer, the singular vectors are computed here from the
conditions L_1 v = L_2 v = 0 with L_{-1}^l-coefficient 1; tau is their torus
norm and gamma = B^1(w, w) their crossing scalar, both computed directly.
For the second layer (levels 7 and 10) the script uses the paper's values
gamma_7 = -700700 and gamma_10 = -1121229484375/192 and the factored torus
norms, which other audits replay.  A nonzero leading coefficient at one
value of d proves the pole order for indeterminate d.
"""

import argparse
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from direct_reconstruction import (  # noqa: E402
    RationalFunction,
    act,
    basis,
    euler_coeffs,
    gram_matrix,
    mat_eval,
    padd,
    peval,
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


def pderiv(poly):
    return tuple(poly[i] * i for i in range(1, len(poly)))


def singular_vector(level, weight):
    """Normalized singular vector of M(1/2, weight) at the given level."""
    parts = list(basis(level))
    rows = []
    for mode in (1, 2):
        images = [act(mode, tuple(-y for y in part)) for part in parts]
        targets = sorted({word for image in images for word in image})
        for word in targets:
            rows.append([peval(image.get(word, ()), weight) for image in images])
    n = len(parts)
    pivots = []
    rank = 0
    for col in range(n):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = 1 / rows[rank][col]
        rows[rank] = [x * inv for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rank])]
        pivots.append(col)
        rank += 1
    free = [col for col in range(n) if col not in pivots]
    assert len(free) == 1, (level, weight, len(free))
    vec = [Fr(0)] * n
    vec[free[0]] = Fr(1)
    for i, col in enumerate(pivots):
        vec[col] = -rows[i][free[0]]
    lead = vec[parts.index((1,) * level)]
    check(f"singular vector of level {level} at {weight}: L_-1^l coefficient nonzero",
          lead != 0)
    return [x / lead for x in vec]


def first_layer_data(level, weight):
    vec = singular_vector(level, weight)
    n = len(vec)
    rho = mat_eval(vertex_matrix(level), weight)
    tau = sum(vec[i] * vec[j] * rho[i][j] for i in range(n) for j in range(n))
    gram = gram_matrix(level)
    form = ()
    for i in range(n):
        for j in range(n):
            if vec[i] and vec[j]:
                form = padd(form, pscale(gram[i][j], vec[i] * vec[j]))
    beta = peval(pderiv(form), weight)
    check(f"crossing scalar of level {level} at {weight} nonzero", beta != 0)
    return tau, beta


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--d", type=Fr, default=Fr(3, 7))
    args = parser.parse_args()
    maxl, d = args.max_level, args.d
    if not 1 <= maxl <= 10:
        parser.error("--max-level must lie in 1..10")
    start = time.time()
    set_external_weight(d)
    coefficients = {0: RationalFunction((Fr(1),), (Fr(1),))}
    for level in range(1, maxl + 1):
        coefficients[level] = reconstruct_F(level, verbose=False)
        print(f"F_{level} reconstructed ({time.time() - start:.0f}s)", flush=True)
    euler = euler_coeffs(maxl)

    def laurent_H(level, point):
        total = {}
        for j in range(level + 1):
            if euler[level - j] == 0:
                continue
            for k, value in coefficients[j].laurent_at(point, 0).items():
                total[k] = total.get(k, Fr(0)) + euler[level - j] * value
        return {k: v for k, v in total.items() if v != 0}

    def value_H(level, point):
        if level < 0:
            return Fr(0)
        laurent = laurent_H(level, point)
        assert all(k >= 0 for k in laurent), (level, point)
        return laurent.get(0, Fr(0))

    p2 = d * (d - 1) * (2 * d - 7) * (2 * d - 1) / 4
    e2 = d * (d - 1) * (3 * d - 14) * (3 * d - 5) / 9
    p15 = (d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
           * (2 * d - 15) * (2 * d - 7) * (2 * d - 5) * (2 * d - 1) / 16)
    p42 = (d * (d - 20) * (d - 13) * (d - 11) * (d - 6) * (d - 1)
           * (2 * d - 57) * (2 * d - 35) * (2 * d - 15) * (2 * d - 7)
           * (2 * d - 5) * (2 * d - 1) * (3 * d - 14) * (3 * d - 5)
           * (6 * d - 55) * (6 * d - 1) / 20736)
    # weight -> (first-layer levels, first level of layer 2, layer-2 data)
    cases = [
        (Fr(0), (1, 6), 11, None),
        (Fr(1, 2), (2, 3), 7, (7, e2 * p15, Fr(-700700))),
        (Fr(1, 16), (2, 4), 10, (10, p2 * p42, Fr(-1121229484375, 192))),
    ]
    for weight, levels, second, layer2 in cases:
        layer1 = []
        for level in levels:
            if level <= maxl:
                tau, beta = first_layer_data(level, weight)
                layer1.append((level, tau, beta))
        for n in range(1, maxl + 1):
            laurent = laurent_H(n, weight)
            order = -min(laurent) if laurent and min(laurent) < 0 else 0
            if n < levels[0]:
                depth, terms = 0, []
            elif n < second:
                depth, terms = 1, [t for t in layer1 if t[0] <= n]
            else:
                depth, terms = 2, [layer2]
            predicted = sum((tau / gamma * value_H(n - level, weight + level)
                             for level, tau, gamma in terms), Fr(0))
            leading = laurent.get(-depth, Fr(0)) if depth else Fr(0)
            check(f"lambda={weight} N={n}: pole order {order} = j_N = {depth}, "
                  f"leading coefficient matches",
                  order == depth and leading == predicted)
    print(f"total {time.time() - start:.0f}s", flush=True)
    if FAILURES:
        print(f"{len(FAILURES)} FAILURES", flush=True)
        sys.exit(1)
    print("ALL PASS", flush=True)


if __name__ == "__main__":
    main()
