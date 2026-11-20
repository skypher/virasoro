#!/usr/bin/env python3
"""Exact replay of Theorem thm:top-layer, Corollary cor:top-layer-sharp, Lemma lem:d-derivatives,
the identities used in Proposition prop:layer-coefficients, the Ising norms of Proposition
prop:ising-double-poles, and enumerations of one-term and two-term windows.

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

One-term windows: for every minimal model with pp' <= 60, every
interior (r, s), k <= 3 and 1 <= M <= 60 in the one-term part of the window,
the sums sum u/D and sum v/D over the labels uv = M (D = (p'u - pv)^2 - m^2)
are checked not to vanish together, and the cases covered by the hypothesis
of Corollary cor:top-layer-sharp are counted.
"""

import argparse
import sys
import time
from fractions import Fraction as Fr
from math import comb, gcd, isqrt

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
    """One-term windows: no common zero of sum u/D and sum v/D."""
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


def layer_coefficients(p, q, r, s, k):
    """Proposition prop:layer-coefficients: {sign: (level, [d^k], [(d-1)^k]) of tau/gamma}."""
    n0, n1, big = q * r - p * s, q * r + p * s, 2 * p * q
    rho, sig = Fr(-n0, 2 * (q - p)), Fr(n0, 2 * (p + q))
    ck = (-1) ** (k // 2) * comb(k - 1, (k - 1) // 2)
    if k % 2:
        j = (k - 1) // 2
        mom = {1: n1 + j * big, -1: (j + 1) * big - n1}
    else:
        j = k // 2
        mom = {1: j * big + n0, -1: j * big - n0}
    lp, lm = layer_levels(p, q, r, s, k)
    out = {}
    for sg, lev in ((1, lp), (-1, lm)):
        mm = mom[sg]
        assert mm > 0 and mm * mm == n0 * n0 + 4 * p * q * lev
        out[sg] = (lev, ck * (sg * rho) ** k, sg ** (k + 1) * ck * sig ** (k - 1) * Fr(mm, 2 * (p + q)))
    return out


def box_set(p, q, u, v, shift):
    """{j : (jp, jp' + shift) in [1-u, u] x [1-v, v]}."""
    return {j for j in range(-u - 1, u + 2)
            if 1 - u <= j * p <= u and 1 - v <= j * q + shift <= v}


def layer_box_identities(ppmax=60, kmax=6):
    """Proposition prop:layer-coefficients: labels, momenta, boxes and first-step sets of the proof."""
    ok = True
    count = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue
            big = 2 * p * q
            for r in range(1, p):
                for s in range(1, q):
                    n0, n1 = q * r - p * s, q * r + p * s
                    if n1 >= p * q:
                        continue
                    lam = kac_weight_num(p, q, r, s)
                    for k in range(1, kmax + 1):
                        count += 1
                        data = layer_coefficients(p, q, r, s, k)
                        j = (k - 1) // 2 if k % 2 else k // 2
                        if k % 2:
                            ends = {1: n1 + j * big, -1: n1 - (j + 1) * big}
                            for sg, (u, v) in ((1, (r + j * p, s + j * q)),
                                               (-1, ((j + 1) * p - r, (j + 1) * q - s))):
                                ok &= kac_weight_num(p, q, u, v) == lam and u * v == data[sg][0]
                                ok &= box_set(p, q, u, v, 0) == set(range(-j, j + 1))
                                ok &= box_set(p, q, u, v, 1) == set(range(-j, j + 1))
                        else:
                            ends = {1: n0 + j * big, -1: n0 - j * big}
                            xk = n1 + (j - 1) * big
                            uk, vk = r + (j - 1) * p, s + (j - 1) * q
                            ok &= box_set(p, q, uk, vk, 0) == set(range(-(j - 1), j))
                            ok &= box_set(p, q, uk, vk, 1) == set(range(-(j - 1), j))
                            for sg, (u, v) in ((1, (r + (2 * j - 1) * p, q - s)),
                                               (-1, (p - r, s + (2 * j - 1) * q))):
                                y = ends[sg]
                                eps = 1 if y > 0 else -1
                                ok &= (u, v) == (eps * (xk + y) // (2 * q), eps * (y - xk) // (2 * p))
                                ok &= (eps * (xk + y)) % (2 * q) == 0 and (eps * (y - xk)) % (2 * p) == 0
                                ok &= box_set(p, q, u, v, 0) == {0} and box_set(p, q, u, v, 1) == {0}
                                ok &= uk * vk + u * v == data[sg][0]
                        # first steps of colliding chains n0 -> ... -> end (reachability by |x| increasing)
                        for sg, y_end in ends.items():
                            elems = [n0 + i * big for i in range(-k - 2, k + 3)] + \
                                    [n1 + i * big for i in range(-k - 2, k + 3)]
                            elems = [x for x in elems if abs(x) <= abs(y_end)]
                            cls = {x: (x - n0) % big == 0 for x in elems}
                            reach = {y_end}
                            for x in sorted(elems, key=abs, reverse=True):
                                if any(cls[y] != cls[x] and abs(y) > abs(x) for y in reach) and x not in reach:
                                    reach.add(x)
                            first = sorted((x - n1) // big for x in reach
                                           if not cls[x] and abs(x) > abs(n0))
                            if k % 2:
                                want = list(range(-j, j + 1)) if sg == 1 else list(range(-j - 1, j))
                            else:
                                want = list(range(-j, j))
                            ok &= first == want
    check(f"Proposition layer-coefficients: labels, boxes, momenta and first steps ({count} cases, "
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
    shifted = taylor_at(poly, Fr(1))
    order1 = next(i for i, x in enumerate(shifted) if x != 0)
    check(f"torus norm of the level-{level} singular vector at {weight}: order {order} at d = 0, "
          f"{order1} at d = 1 (layer {layer})", order == layer and order1 == layer)


def taylor_at(poly, x0):
    """Taylor coefficients of a polynomial (ascending coefficients) at x0."""
    out = []
    cur = list(poly)
    while cur:
        nxt = [Fr(0)] * (len(cur) - 1)
        acc = cur[-1]
        for i in range(len(cur) - 2, -1, -1):
            nxt[i] = acc
            acc = cur[i] + acc * x0
        out.append(acc)
        cur = nxt
    return out


def two_term_layers(ppmax=60, kmax=6):
    """Two-term windows and Corollary cor:top-layer-sharp (odd k)."""
    top = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q != p and gcd(p, q) == 1:
                for r in range(1, p):
                    for s in range(1, q):
                        if q * r + p * s < p * q:
                            top = max(top, min(layer_levels(p, q, r, s, kmax + 1)))
    divs = [[] for _ in range(top + 1)]
    for u in range(1, top + 1):
        for m in range(u, top + 1, u):
            divs[m].append(u)
    cases = fails = covered = cover_bad = 0
    for p in range(2, ppmax):
        for q in range(2, ppmax // p + 1):
            if q == p or gcd(p, q) != 1:
                continue

            def k_and_l(big_m, mom):
                kk = ll = Fr(0)
                for u in divs[big_m]:
                    v = big_m // u
                    f, g = q * u - p * v, q * u + p * v
                    den = mom * mom - f * f
                    assert den != 0
                    kk += Fr(-2 * p * q * f, (q - p) * den)
                    ll += Fr(2 * p * q * g, (p + q) * den)
                return kk, ll

            for r in range(1, p):
                for s in range(1, q):
                    n0, n1 = q * r - p * s, q * r + p * s
                    if n1 >= p * q:
                        continue
                    for k in range(1, kmax + 1):
                        data = layer_coefficients(p, q, r, s, k)
                        nxt = min(layer_levels(p, q, r, s, k + 1))
                        for n in range(max(data[1][0], data[-1][0]) + 1, nxt):
                            c0 = c1 = Fr(0)
                            ls = {}
                            in_range = True
                            ks = {}
                            for sg in (1, -1):
                                lev, rk, rtk = data[sg]
                                mom = isqrt(n0 * n0 + 4 * p * q * lev)
                                kk, ll = k_and_l(n - lev, mom)
                                c0 += rk * kk
                                c1 += rtk * ll
                                ls[sg] = ll
                                ks[sg] = kk
                                in_range &= max(p, q) * (n - lev) < mom + min(p, q)
                            cases += 1
                            fails += c0 == 0 and c1 == 0
                            if in_range:
                                covered += 1
                                if k % 2:
                                    cover_bad += not (ls[1] > 0 and ls[-1] > 0 and c1 != 0)
                                else:
                                    cover_bad += not (ks[1] < 0 and ks[-1] < 0 and c0 != 0)
    print(f"two-term window cases (k <= {kmax}) {cases}, covered by the corollary {covered}, "
          f"criterion fails in {fails}", flush=True)
    check(f"two-term criterion (pp' <= {ppmax}, k <= {kmax}); corollary range: L+, L- > 0 (odd k), "
          f"K+, K- < 0 (even k)",
          fails == 0 and cover_bad == 0 and cases > 0)


def ising_layer_two():
    """Proposition prop:layer-coefficients against the Ising norms gamma_7, gamma_10, gamma_11
    (Proposition prop:ising-double-poles)."""
    def pmulx(a, b):
        out = [Fr(0)] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] += x * y
        return out

    def lin(*roots_scaled):
        poly = [Fr(1)]
        for a, c in roots_scaled:  # factor (a d - c)
            poly = pmulx(poly, [Fr(-c), Fr(a)])
        return poly

    u = lin((1, 0), (1, 20), (1, 13), (1, 11), (1, 6), (1, 1))
    e2 = [x / 9 for x in lin((1, 0), (1, 1), (3, 14), (3, 5))]
    p15 = [x / 16 for x in pmulx(u, lin((2, 15), (2, 7), (2, 5), (2, 1)))]
    p2 = [x / 4 for x in lin((1, 0), (1, 1), (2, 7), (2, 1))]
    p16 = [x / 64 for x in pmulx(u, lin((2, 57), (2, 35), (2, 15), (2, 7), (2, 5), (2, 1)))]
    p42 = [x / 324 for x in pmulx(p16, lin((3, 14), (3, 5), (6, 55), (6, 1)))]
    for name, tau, gamma, (r, s), sg in (("gamma_7", pmulx(e2, p15), Fr(-700700), (2, 1), -1),
                                         ("gamma_10", pmulx(p2, p42), Fr(-1121229484375, 192), (1, 2), 1)):
        lev, rk, rtk = layer_coefficients(3, 4, r, s, 2)[sg]
        a0, a1 = taylor_at(tau, Fr(0)), taylor_at(tau, Fr(1))
        ok = a0[0] == a0[1] == 0 and a0[2] / gamma == rk and a1[0] == a1[1] == 0 and a1[2] / gamma == rtk
        check(f"Ising {name} (level {lev}): [d^2] tau/gamma = {rk}, [(d-1)^2] tau/gamma = {rtk}", ok)

    def kac_family(big_r, big_s):
        """Monic P_{R,S}(b_0, d) of Proposition prop:two-term-criteria at (p, p') = (3, 4)."""
        poly = [Fr(1)]
        for a in range(1, 2 * big_r, 2):
            for l in range(1, 2 * big_s, 2):
                for x in (4 * a - 3 * l, 4 * a + 3 * l):
                    poly = pmulx(poly, [-Fr(x * x - 1, 48), Fr(1)])
        return poly

    check("Proposition prop:ising-double-poles: P_{2,1} P_{1,5} = E_2 P_{1,5} and P_{1,2} P_{4,2} "
          "equal the factored torus norms",
          pmulx(kac_family(2, 1), kac_family(1, 5)) == pmulx(e2, p15)
          and pmulx(kac_family(1, 2), kac_family(4, 2)) == pmulx(p2, p42))
    tau11 = pmulx(kac_family(1, 1), kac_family(2, 5))
    gamma11 = Fr(-2477917160468750, 6561)
    lev, rk, rtk = layer_coefficients(3, 4, 1, 1, 2)[-1]
    a0, a1 = taylor_at(tau11, Fr(0)), taylor_at(tau11, Fr(1))
    check(f"Ising gamma_11 (level {lev}) of Proposition prop:ising-double-poles: "
          f"[d^2] tau/gamma = {rk}, [(d-1)^2] tau/gamma = {rtk}",
          lev == 11 and a0[0] == a0[1] == 0 and a0[2] / gamma11 == rk
          and a1[0] == a1[1] == 0 and a1[2] / gamma11 == rtk)


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
    two_term_layers()
    layer_box_identities()
    ising_layer_two()
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
