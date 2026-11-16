#!/usr/bin/env python3
"""Exact replay of Theorem thm:top-layer, Corollary cor:top-layer-sharp, Lemmas lem:d-derivatives
and lem:tau-order, and the enumerations of Remark rem:top-layer-beyond.

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

Lemma lem:d-derivatives is checked at c = 1/2 for M <= 6 at four internal
weights: H_M(1/2, h, d) is computed from G_M and rho_M at 2M + 3 values of d
and interpolated, and its values and derivatives at d = 0, 1 are compared with
the closed forms.

Remark rem:top-layer-beyond: for every minimal model with pp' <= 60, every
interior (r, s), k <= 3 and 1 <= M <= 60 in the one-term part of the window,
the sums sum u/D and sum v/D over the labels uv = M (D = (p'u - pv)^2 - m^2)
are checked not to vanish together, and the cases covered by the hypothesis
of Corollary cor:top-layer-sharp are counted.
"""

import argparse
import sys
import time
from fractions import Fraction as Fr
from math import gcd, isqrt

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from direct_reconstruction import (  # noqa: E402
    RationalFunction,
    act,
    basis,
    det_and_trace_inv,
    euler_coeffs,
    gram_matrix,
    lagrange_interp,
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


def d_derivative_checks():
    """Lemma lem:d-derivatives at c = 1/2 (t = b_0^2 = -4/3)."""
    t = Fr(-4, 3)
    euler = euler_coeffs(6)
    grams = {level: gram_matrix(level) for level in range(1, 7)}
    for h0, mmax in ((Fr(15, 2), 6), (Fr(3, 7), 6), (Fr(161, 16), 6), (Fr(1), 4)):
        for m in range(1, mmax + 1):
            points = []
            for i in range(2 * m + 3):
                dval = Fr(i + 2, 3)
                set_external_weight(dval)
                f = [Fr(1)]
                for level in range(1, m + 1):
                    det, tr = det_and_trace_inv(mat_eval(grams[level], h0),
                                                mat_eval(vertex_matrix(level), h0))
                    assert det != 0
                    f.append(tr)
                points.append((dval, sum(euler[j] * f[m - j] for j in range(m + 1))))
            poly = lagrange_interp(points)
            deriv = tuple(poly[i] * i for i in range(1, len(poly)))
            labels = [(r, m // r) for r in range(1, m + 1) if m % r == 0]
            k0 = -sum((r * t + s) / (2 * (t + 1) * (h0 - Fr((4 * r - 3 * s) ** 2 - 1, 48)))
                      for r, s in labels)
            k1 = sum((r * t - s) / (2 * (t - 1) * (h0 - Fr((4 * r - 3 * s) ** 2 - 1, 48)))
                     for r, s in labels)
            check(f"d-derivatives at h={h0}, M={m}",
                  len(poly) <= 2 * m + 1 and peval(poly, Fr(0)) == 0
                  and peval(poly, Fr(1)) == 0 and peval(deriv, Fr(0)) == k0
                  and peval(deriv, Fr(1)) == k1)


def layer_levels(p, q, r, s, k):
    n0, pq = q * r - p * s, p * q
    if k % 2 == 0:
        j = k // 2
        return j * (j * pq + n0), j * (j * pq - n0)
    j = (k - 1) // 2
    return (r + j * p) * (s + j * q), ((j + 1) * p - r) * ((j + 1) * q - s)


def window_criterion(ppmax=60, kmax=3, mmax=60):
    """Remark rem:top-layer-beyond: no common zero of sum u/D and sum v/D."""
    cases = covered = zeros = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue
            for r in range(1, p):
                for s in range(1, q):
                    if q * r + p * s >= p * q:
                        continue
                    for k in range(1, kmax + 1):
                        lo, hi = sorted(layer_levels(p, q, r, s, k))
                        m2 = (q * r - p * s) ** 2 + 4 * p * q * lo
                        m = isqrt(m2)
                        assert m * m == m2
                        for big_m in range(1, min(mmax, hi - lo - 1) + 1):
                            su = sv = Fr(0)
                            for u in range(1, big_m + 1):
                                if big_m % u == 0:
                                    v = big_m // u
                                    den = (q * u - p * v) ** 2 - m2
                                    assert den != 0
                                    su += Fr(u, den)
                                    sv += Fr(v, den)
                            cases += 1
                            covered += min(p, q) * big_m < m + max(p, q)
                            zeros += su == 0 and sv == 0
    print(f"one-term window cases {cases}, covered by Corollary {covered}, "
          f"common zeros {zeros}", flush=True)
    check("no common zero of sum u/D and sum v/D (pp' <= 60, k <= 3, M <= 60)",
          zeros == 0 and cases > 0)


def box_zero_count(p, q, u, v):
    """Number of j with j(p, q) in [1-u, u] x [1-v, v]."""
    return sum(1 for j in range(-u - 1, u + 2)
               if 1 - u <= j * p <= u and 1 - v <= j * q <= v)


def kac_weight_num(p, q, u, v):
    """4pq h_{u,v}(b_*) + (q-p)^2 = (q u - p v)^2."""
    return (q * u - p * v) ** 2


def tau_order_identities(ppmax=60, kmax=6):
    """Lemma lem:tau-order: labels, levels, weights and zero counts of the proof."""
    ok = True
    count = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue
            for r in range(1, p):
                for s in range(1, q):
                    if q * r + p * s >= p * q:
                        continue
                    lam = kac_weight_num(p, q, r, s)
                    for k in range(1, kmax + 1):
                        count += 1
                        if k % 2:
                            j = (k - 1) // 2
                            for u, v in ((r + j * p, s + j * q),
                                         ((j + 1) * p - r, (j + 1) * q - s)):
                                ok &= kac_weight_num(p, q, u, v) == lam
                                ok &= u * v in layer_levels(p, q, r, s, k)
                                ok &= box_zero_count(p, q, u, v) == k
                        else:
                            j = k // 2
                            lminus = layer_levels(p, q, r, s, k - 1)[1]
                            # lambda + l^-_{2j-1} = h_{jp-r, -(jq-s)}: momentum 2jpq - n1
                            xi = (q * (j * p - r) + p * (j * q - s)) ** 2
                            lp, lm = layer_levels(p, q, r, s, k)
                            for (u, v), target in (((r, 2 * j * q - s), lp),
                                                   ((2 * j * p - r, s), lm)):
                                ok &= kac_weight_num(p, q, u, v) == xi
                                ok &= u * v == target - lminus
                                ok &= box_zero_count(p, q, u, v) == 1
    check(f"Lemma tau-order: labels, levels, weights and zero counts ({count} cases, "
          f"pp' <= {ppmax}, k <= {kmax})", ok and count > 0)


def tau_order_direct(weight, level, layer):
    """Order at d = 0 of the torus norm of the singular vector, by direct computation at c = 1/2."""
    vec = singular_vector(level, weight)
    n = len(vec)
    points = []
    for i in range(2 * level + 1):
        dval = Fr(i + 1, 2)
        set_external_weight(dval)
        rho = mat_eval(vertex_matrix(level), weight)
        points.append((dval, sum(vec[a] * vec[b] * rho[a][b] for a in range(n) for b in range(n))))
    poly = lagrange_interp(points)
    order = next(i for i, x in enumerate(poly) if x != 0)
    check(f"torus norm of the level-{level} singular vector at {weight}: order {order} at d = 0 "
          f"(layer {layer})", order == layer)


def two_term_first_layer(ppmax=60):
    """Remark rem:top-layer-beyond, two-term part of the first layer."""
    cases = fails = 0

    def sums(p, q, big_m, m):
        sk = sl = Fr(0)
        for u in range(1, big_m + 1):
            if big_m % u == 0:
                v = big_m // u
                f, g = q * u - p * v, q * u + p * v
                den = f * f - m * m
                assert den != 0
                sk += Fr(f, den)
                sl += Fr(g, den)
        return sk, sl

    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue
            pq = p * q
            for r in range(1, p):
                for s in range(1, q):
                    n1 = q * r + p * s
                    if n1 >= pq:
                        continue
                    lp, lm = r * s, (p - r) * (q - s)
                    for n in range(max(lp, lm) + 1, min(layer_levels(p, q, r, s, 2))):
                        skp, slp = sums(p, q, n - lp, n1)
                        skm, slm = sums(p, q, n - lm, 2 * pq - n1)
                        cases += 1
                        fails += skp == skm and n1 * slp + (2 * pq - n1) * slm == 0
    print(f"two-term first-layer cases {cases}, criterion fails in {fails}", flush=True)
    check("two-term first-layer criterion (pp' <= 60)", fails == 0 and cases > 0)


def two_term_second_layer(ppmax=60):
    """Remark rem:top-layer-beyond, two-term part of the second layer (Proposition prop:second-layer)."""
    cases = hyp_fail = fails = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue
            t = Fr(-q, p)

            def eta(u, v):
                return 1 - u * u + Fr(v * v - 1) / (t * t)

            def rho(u, v):
                return -(u * t + v) / (2 * (t + 1))

            def rhop(u, v):
                return (u * t - v) / (2 * (t - 1))

            def k_and_l(big_m, xnum):
                kk = ll = Fr(0)
                for u in range(1, big_m + 1):
                    if big_m % u == 0:
                        v = big_m // u
                        den = Fr(xnum - kac_weight_num(p, q, u, v), 4 * p * q)
                        assert den != 0
                        kk += -(u * t + v) / (2 * (t + 1) * den)
                        ll += (u * t - v) / (2 * (t - 1) * den)
                return kk, ll

            for r in range(1, p):
                for s in range(1, q):
                    if q * r + p * s >= p * q:
                        continue
                    lam = kac_weight_num(p, q, r, s)
                    hi2 = max(layer_levels(p, q, r, s, 2))
                    l3 = min(layer_levels(p, q, r, s, 3))
                    for kap in ((r, s), (p - r, q - s)):
                        lk = kap[0] * kap[1]
                        xi = lam + 4 * p * q * lk
                        for n in range(hi2 + 1, l3):
                            big_m = n - lk
                            gs = [(u, v) for u in range(1, big_m + 1)
                                  for v in range(1, big_m // u + 1)
                                  if kac_weight_num(p, q, u, v) == xi]
                            cases += 1
                            if any(u >= p and v >= q for u, v in gs) or \
                                    any(eta(u, v) == eta(*kap) for u, v in gs):
                                hyp_fail += 1
                                continue
                            c0 = c1 = Fr(0)
                            for u, v in gs:
                                if big_m > u * v:
                                    kk, ll = k_and_l(big_m - u * v, xi + 4 * p * q * u * v)
                                    c0 += rho(u, v) * kk / (eta(*kap) - eta(u, v))
                                    c1 += rhop(u, v) * ll / (eta(*kap) - eta(u, v))
                            fails += c0 == 0 and c1 == 0
    print(f"two-term second-layer cases {cases}, hypothesis failures {hyp_fail}, "
          f"criterion fails in {fails}", flush=True)
    check("two-term second-layer criterion (pp' <= 60)",
          hyp_fail == 0 and fails == 0 and cases > 0)


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
    d_derivative_checks()
    window_criterion()
    two_term_first_layer()
    two_term_second_layer()
    tau_order_identities()
    for weight, level, layer in ((Fr(0), 1, 1), (Fr(0), 6, 1), (Fr(1, 2), 2, 1),
                                 (Fr(1, 2), 3, 1), (Fr(1, 16), 2, 1), (Fr(1, 16), 4, 1),
                                 (Fr(1, 2), 7, 2)):
        tau_order_direct(weight, level, layer)
    print(f"total {time.time() - start:.0f}s", flush=True)
    if FAILURES:
        print(f"{len(FAILURES)} FAILURES", flush=True)
        sys.exit(1)
    print("ALL PASS", flush=True)


if __name__ == "__main__":
    main()
