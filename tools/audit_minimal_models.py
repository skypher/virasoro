#!/usr/bin/env python3
"""Direct test of exact pole orders j_N(lambda) at seven minimal models (Remark rem:top-layer-beyond).

Usage: python3 -u tools/audit_minimal_models.py [NMAX] [D] [-h|--help]   (defaults 10, 11/13)

For each (p,p') in MODELS ((2,3) one level further, into the two-term part of
its second layer), sets c = 1 - 6(p'-p)^2/(pp') in tools/direct_reconstruction.py,
reconstructs F_1..F_NMAX exactly as rational functions of the internal weight at external weight
D, and for every interior weight lambda = h_{r,s} compares the pole order of H_N at lambda with
the Jantzen depth j_N(lambda) of Theorem 5.8.  Prints MISMATCH lines if any.
A nonzero leading coefficient at one value of D proves the pole order for
indeterminate d; D must avoid the Kac weights of the models (for instance
d = 3/7 is h_{1,7} at (p,p') = (2,7)), which 11/13 does.
"""
import sys
import time
from fractions import Fraction as Fr
from math import gcd
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import direct_reconstruction as dr  # noqa: E402

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
D = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(11, 13)
MODELS = [(3, 4, NMAX), (2, 3, NMAX + 1), (2, 5, NMAX), (2, 7, NMAX), (3, 5, NMAX),
          (4, 5, NMAX), (2, 9, NMAX), (3, 7, NMAX)]


def levels(p, q, r, s, k):
    n0, P = q * r - p * s, p * q
    if k % 2 == 0:
        j = k // 2
        return j * (j * P + n0), j * (j * P - n0)
    j = (k - 1) // 2
    return (r + j * p) * (s + j * q), ((j + 1) * p - r) * ((j + 1) * q - s)


def depth(p, q, r, s, n):
    k = 0
    while min(levels(p, q, r, s, k + 1)) <= n:
        k += 1
    return k


t0 = time.time()
mismatch = checked = 0
for p, q, nmax in MODELS:
    assert gcd(p, q) == 1
    dr.C_CHARGE = 1 - Fr(6 * (q - p) ** 2, p * q)
    dr.act.cache_clear()
    dr.set_external_weight(D)
    coef = {0: dr.RationalFunction((Fr(1),), (Fr(1),))}
    for n in range(1, nmax + 1):
        coef[n] = dr.reconstruct_F(n, verbose=False)
        print(f'(p,q)=({p},{q}) c={dr.C_CHARGE}: F_{n} reconstructed ({time.time() - t0:.0f}s)', flush=True)
    eta = dr.euler_coeffs(nmax)
    for r in range(1, p):
        for s in range(1, q):
            if q * r + p * s >= p * q:
                continue
            lam = Fr((q * r - p * s) ** 2 - (q - p) ** 2, 4 * p * q)
            for n in range(1, nmax + 1):
                tot = {}
                for j in range(n + 1):
                    if eta[n - j]:
                        for kk, v in coef[j].laurent_at(lam, 0).items():
                            tot[kk] = tot.get(kk, Fr(0)) + eta[n - j] * v
                tot = {kk: v for kk, v in tot.items() if v != 0}
                order = -min(tot) if tot and min(tot) < 0 else 0
                jn = depth(p, q, r, s, n)
                checked += 1
                tag = 'ok' if order == jn else 'MISMATCH'
                mismatch += order != jn
                print(f'{tag} (p,q)=({p},{q}) (r,s)=({r},{s}) lambda={lam} N={n}: order {order}, j_N {jn}',
                      flush=True)


def second_layer_check():
    """Proposition prop:layer-coefficients with Theorem thm:top-layer at (p,p') = (2,3), lambda = 0:
    Taylor coefficients at d = 0, 1 of the double-pole coefficient for N = 7, 8, 9 (direct)."""
    mismatch = 0
    p, q = 2, 3
    t = Fr(-q, p)


    def h(u, v):
        return Fr((q * u - p * v) ** 2 - (q - p) ** 2, 4 * p * q)


    def eta(u, v):
        return 1 - u * u + Fr(v * v - 1) / (t * t)


    def rho(u, v):
        return -(u * t + v) / (2 * (t + 1))


    def rhop(u, v):
        return (u * t - v) / (2 * (t - 1))


    def K(M, x):
        if M == 0:
            return Fr(0)
        return -sum((u * t + M // u) / (2 * (t + 1) * (x - h(u, M // u)))
                    for u in range(1, M + 1) if M % u == 0)


    def L(M, x):
        if M == 0:
            return Fr(0)
        return sum((u * t - M // u) / (2 * (t - 1) * (x - h(u, M // u)))
                   for u in range(1, M + 1) if M % u == 0)


    # Proposition prop:layer-coefficients, k = 2, (r,s) = (1,1): n0 = 1, levels 7 (+), 5 (-)
    n0, rho_l, sig = 1, Fr(-1, 2), Fr(1, 10)
    rp, rm = -rho_l ** 2, -rho_l ** 2
    rtp = (+1) * (-1) * sig * Fr(12 + n0, 2 * 5)
    rtm = (-1) * (-1) * sig * Fr(12 - n0, 2 * 5)
    print('r- =', rm, ' r+ =', rp, " r~- =", rtm, " r~+ =", rtp, flush=True)
    assert h(1, 1) == 0 and h(1, 4) == 1 and h(3, 2) == 1


    def taylor(poly, x0):
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


    dr.C_CHARGE = Fr(0)  # (p,p') = (2,3)
    dr.act.cache_clear()
    t0 = time.time()
    NMAX = 9
    eta_e = dr.euler_coeffs(NMAX)
    pts = {7: [], 8: [], 9: []}
    for i in range(2 * NMAX + 3):
        dval = Fr(2 * i + 3, 11)
        dr.set_external_weight(dval)
        coef = {0: dr.RationalFunction((Fr(1),), (Fr(1),))}
        for n in range(1, NMAX + 1):
            coef[n] = dr.reconstruct_F(n, verbose=False)
        for N in (7, 8, 9):
            lead = sum(eta_e[N - j] * coef[j].laurent_at(Fr(0), 0).get(-2, Fr(0)) for j in range(N + 1))
            pts[N].append((dval, lead))
        print(f'd = {dval}: done ({i + 1}/{2 * NMAX + 3}, {time.time() - t0:.0f}s)', flush=True)
    fail = 0
    for N in (7, 8, 9):
        poly = dr.lagrange_interp(pts[N])
        a0, a1 = taylor(poly, Fr(0)), taylor(poly, Fr(1))
        a0 += [Fr(0)] * 4
        a1 += [Fr(0)] * 4
        if N == 7:
            ok = a0[0] == a0[1] == 0 and a0[2] == rp and a1[0] == a1[1] == 0 and a1[2] == rtp
            print(('PASS' if ok else 'FAIL'), f'N=7: [d^2] = {a0[2]} (pred {rp}), [(d-1)^2] = {a1[2]} (pred {rtp})',
                  flush=True)
        else:
            pk = rm * K(N - 5, Fr(5)) + rp * K(N - 7, Fr(7))
            pl = rtm * L(N - 5, Fr(5)) + rtp * L(N - 7, Fr(7))
            ok = (a0[0] == a0[1] == a0[2] == 0 and a0[3] == pk
                  and a1[0] == a1[1] == a1[2] == 0 and a1[3] == pl)
            print(('PASS' if ok else 'FAIL'), f'N={N}: [d^3] = {a0[3]} (pred {pk}), [(d-1)^3] = {a1[3]} (pred {pl})',
                  flush=True)
        fail += not ok
    mismatch += fail
    return mismatch


mismatch += second_layer_check()
print(f'checked {checked}, mismatches {mismatch}, total {time.time() - t0:.0f}s', flush=True)
if mismatch:
    sys.exit(1)
print('ALL PASS', flush=True)
