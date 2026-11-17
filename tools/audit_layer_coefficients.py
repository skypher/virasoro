#!/usr/bin/env python3
"""Exact check of Proposition prop:layer-coefficients against the generic recursion.

Usage: python3 -u tools/audit_layer_coefficients.py [-h|--help]

For a minimal model (p,p'), an interior label (r,s) and a level N = l^pm_k, the generic residue
recursion (Proposition prop:generic-recursion) is expanded exactly in Laurent series in
s = b^2 - b_*^2, with d = e or d = 1 + e truncated at e^k.  The coefficient of (Delta-lambda)^-k of
H_N(c_*, Delta, d) is sum_g [s^0] B_g (h_g - lambda)^(k-1) over the labels g with h_g(b_*) = lambda
(Definition def:collision-moments); the script checks that the analogous sums with exponents k, k+1
vanish, that the coefficients of e^i, i < k, vanish, and that the coefficient of e^k equals the
closed form of the proposition.  All arithmetic is in exact rationals.
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)

L = 10            # relative precision of the base series
FAILURES = []


def layer_levels(p, q, r, s, k):
    n0, pq = q * r - p * s, p * q
    if k % 2 == 0:
        j = k // 2
        return j * (j * pq + n0), j * (j * pq - n0)
    j = (k - 1) // 2
    return (r + j * p) * (s + j * q), ((j + 1) * p - r) * ((j + 1) * q - s)


def closed_form(p, q, r, s, k, sign, at_one):
    n0, n1, big = q * r - p * s, q * r + p * s, 2 * p * q
    ck = (-1) ** (k // 2) * comb(k - 1, (k - 1) // 2)
    if not at_one:
        return ck * (sign * Fr(-n0, 2 * (q - p))) ** k
    if k % 2:
        j = (k - 1) // 2
        mom = n1 + j * big if sign == 1 else (j + 1) * big - n1
    else:
        j = k // 2
        mom = j * big + sign * n0
    return sign ** (k + 1) * ck * Fr(n0, 2 * (p + q)) ** (k - 1) * Fr(mom, 2 * (p + q))


# Laurent series: (v, [c_v, c_{v+1}, ...]) with scalar entries; d-series: entries are lists of length D+1.
def s_strip(a):
    v, c = a
    i = 0
    while i < len(c) and c[i] == 0:
        i += 1
    return (v + i, c[i:])


def s_mul(a, b):
    va, ca = a
    vb, cb = b
    n = min(len(ca), len(cb))
    res = [Fr(0)] * n
    for i in range(n):
        if ca[i]:
            for j in range(n - i):
                res[i + j] += ca[i] * cb[j]
    return (va + vb, res)


def s_add(a, b, sign=1):
    va, ca = a
    vb, cb = b
    v = min(va, vb)
    prec = min(va + len(ca), vb + len(cb))
    res = [Fr(0)] * max(prec - v, 0)
    for i, x in enumerate(ca):
        if va + i < prec:
            res[va + i - v] += x
    for i, x in enumerate(cb):
        if vb + i < prec:
            res[vb + i - v] += sign * x
    return s_strip((v, res))


def s_inv(a):
    v, c = s_strip(a)
    assert c, "inverse of a zero series"
    n = len(c)
    res = [Fr(0)] * n
    res[0] = 1 / c[0]
    for m in range(1, n):
        res[m] = -sum(c[j] * res[m - j] for j in range(1, m + 1)) / c[0]
    return (-v, res)


def check_case(p, q, r, s, N, at_one):
    t_star = Fr(-q, p)
    lam = Fr((q * r - p * s) ** 2 - (q - p) ** 2, 4 * p * q)
    k = 0
    while min(layer_levels(p, q, r, s, k + 1)) <= N:
        k += 1
    D = k
    tser = (0, [t_star, Fr(1)] + [Fr(0)] * (L + 40))

    def d_from_s(a):
        return (a[0], [[x] + [Fr(0)] * D for x in a[1]])

    def d_strip(a):
        v, c = a
        i = 0
        while i < len(c) and not any(c[i]):
            i += 1
        return (v + i, c[i:])

    def d_mul(a, b, dc=D):
        va, ca = a
        vb, cb = b
        n = min(len(ca), len(cb))
        res = [[Fr(0)] * (D + 1) for _ in range(n)]
        for i in range(n):
            for e1, x in enumerate(ca[i]):
                if x:
                    for j in range(n - i):
                        row = res[i + j]
                        for e2 in range(min(D, dc) + 1 - e1):
                            y = cb[j][e2]
                            if y:
                                row[e1 + e2] += x * y
        return (va + vb, res)

    def d_scale(a, sc):
        va, ca = a
        vb, cb = sc
        n = min(len(ca), len(cb))
        res = [[Fr(0)] * (D + 1) for _ in range(n)]
        for i in range(n):
            for j in range(n - i):
                y = cb[j]
                if y:
                    for e in range(D + 1):
                        if ca[i][e]:
                            res[i + j][e] += ca[i][e] * y
        return (va + vb, res)

    def d_add(a, b):
        va, ca = a
        vb, cb = b
        v = min(va, vb)
        prec = min(va + len(ca), vb + len(cb))
        res = [[Fr(0)] * (D + 1) for _ in range(max(prec - v, 0))]
        for vv, cc in ((va, ca), (vb, cb)):
            for i, row in enumerate(cc):
                if vv + i < prec:
                    for e in range(D + 1):
                        res[vv + i - v][e] += row[e]
        return d_strip((v, res))

    def d_trunc(a, dc):
        return (a[0], [[x if e <= dc else Fr(0) for e, x in enumerate(row)] for row in a[1]])

    inv4t = s_inv(s_mul((0, [Fr(4)] + [Fr(0)] * (L + 40)), tser))
    hcache = {}

    def hser(u, v):
        if (u, v) not in hcache:
            c0 = (t_star + 1) ** 2 - (u * t_star + v) ** 2
            c1 = 2 * (t_star + 1) - 2 * u * (u * t_star + v)
            c2 = Fr(1 - u * u)
            num = (0, [c0, c1, c2] + [Fr(0)] * (L + 37))
            hcache[(u, v)] = (lambda z: (z[0], z[1][:L]))(s_mul(num, inv4t))
        return hcache[(u, v)]

    rcache = {}

    def rser(u, v):
        if (u, v) in rcache:
            return rcache[(u, v)]
        a_ser = (0, [Fr(1, 2)] + [Fr(0)] * (L + 20))
        tp = (0, [Fr(1)] + [Fr(0)] * (L + 20))
        for _ in range(2 * u * v - 1):
            tp = s_mul(tp, (0, tser[1][:L + 21]))
        a_ser = s_mul(a_ser, tp)
        for a in range(1 - u, u + 1):
            for c in range(1 - v, v + 1):
                if (a, c) in ((0, 0), (u, v)):
                    continue
                c0 = a * t_star + c
                if c0 == 0:
                    fac = (-1, [Fr(1, a)] + [Fr(0)] * (L + 20))
                else:
                    ratio, ser = Fr(-a) / c0, [1 / c0]
                    for _ in range(L + 20):
                        ser.append(ser[-1] * ratio)
                    fac = (0, ser)
                a_ser = s_mul(a_ser, fac)
        a_ser = s_strip(a_ser)
        poly = (0, [[Fr(1)] + [Fr(0)] * D] + [[Fr(0)] * (D + 1) for _ in range(L + 19)])
        for kk in range(1, 2 * u, 2):
            for ll in range(1, 2 * v, 2):
                for sg in (1, -1):
                    hs = hser(kk, sg * ll)
                    if at_one:
                        hs = s_add(hs, (0, [Fr(1)] + [Fr(0)] * (L + 40)), -1)
                    hl = (hs[0], hs[1] + [Fr(0)] * 30)
                    a1 = d_scale(poly, (hl[0], hl[1][:len(poly[1])]))
                    shifted = (poly[0], [[-x for x in ([Fr(0)] + row[:D])] for row in poly[1]])
                    poly = d_add(a1, shifted)
        res = d_strip(d_mul(d_from_s((a_ser[0], a_ser[1][:L])), poly))
        rcache[(u, v)] = (res[0], res[1][:L])
        return rcache[(u, v)]

    labels = [(u, v) for u in range(1, N + 1) for v in range(1, N // u + 1)]
    one = (0, [[Fr(1)] + [Fr(0)] * D] + [[Fr(0)] * (D + 1) for _ in range(L + 30)])
    memo, dens = {}, {}

    def inv_den(g, f):
        if (g, f) not in dens:
            z = s_add(hser(*g), (0, [Fr(g[0] * g[1])] + [Fr(0)] * (L - 1)))
            dens[(g, f)] = (lambda w: (w[0], w[1][:L]))(s_inv(s_add(z, hser(*f), -1)))
        return dens[(g, f)]

    def H(M, g, dc):
        if M == 0:
            return d_trunc(one, dc)
        if dc <= 0:
            return (L + 30, [])
        if (M, g, dc) in memo:
            return memo[(M, g, dc)]
        acc = None
        for f in labels:
            if f[0] * f[1] > M:
                continue
            sub = H(M - f[0] * f[1], f, dc - 1)
            if not sub[1]:
                continue
            term = d_mul(d_trunc(rser(*f), dc), d_scale(sub, inv_den(g, f)), dc)
            acc = term if acc is None else d_add(acc, term)
        acc = (L + 30, []) if acc is None else d_trunc(acc, dc)
        memo[(M, g, dc)] = acc
        return acc

    def h_exact(u, v):
        return ((t_star + 1) ** 2 - (u * t_star + v) ** 2) / (4 * t_star)

    cls = [g for g in labels if h_exact(*g) == lam]
    sums = {}
    for jj in range(k - 1, k + 2):
        tot = [Fr(0)] * (D + 1)
        for g in cls:
            delta = s_add(hser(*g), (0, [lam] + [Fr(0)] * (L + 30)), -1)
            dj = (0, [Fr(1)] + [Fr(0)] * (L + 30))
            for _ in range(jj):
                dj = s_mul(dj, delta)
            B = d_mul(d_trunc(rser(*g), D), H(N - g[0] * g[1], g, D - 1))
            if not B[1]:
                continue
            v, c = d_scale(B, dj)
            if v + len(c) <= 0:
                raise RuntimeError("precision too low")
            if v <= 0:
                for e in range(D + 1):
                    tot[e] += c[-v][e]
        sums[jj] = tot
    lp, lm = layer_levels(p, q, r, s, k)
    sign = 1 if N == lp else -1
    want = closed_form(p, q, r, s, k, sign, at_one)
    lead = sums[k - 1]
    ok = (all(x == 0 for x in lead[:k]) and lead[k] == want
          and all(x == 0 for jj in (k, k + 1) for x in sums[jj]))
    return ok, k, lead[k], want


def main():
    t0 = time.time()
    cases = [((2, 3, 1, 1), (1, 2, 5, 7, 12, 15, 22, 26)),
             ((2, 5, 1, 2), (2, 3, 9, 11, 21, 24)),
             ((3, 4, 2, 1), (2, 3, 7, 17, 25, 28)),
             ((2, 7, 1, 3), (3, 4, 13, 15, 30, 33))]
    for (p, q, r, s), levels in cases:
        for N in levels:
            for at_one in (False, True):
                ok, k, got, want = check_case(p, q, r, s, N, at_one)
                tag = "(d-1)" if at_one else "d"
                print(("PASS" if ok else "FAIL") + f" (p,p')=({p},{q}) (r,s)=({r},{s}) N={N} k={k}: "
                      f"[{tag}^{k}] = {got} (closed form {want}) ({time.time() - t0:.0f}s)", flush=True)
                if not ok:
                    FAILURES.append((p, q, r, s, N, at_one))
    if FAILURES:
        print(f"{len(FAILURES)} FAILURES", flush=True)
        sys.exit(1)
    print("ALL PASS", flush=True)


if __name__ == "__main__":
    main()
