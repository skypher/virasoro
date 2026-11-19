#!/usr/bin/env python3
# py-rules-ok: small exact check (levels <= 7, under a minute); reuses the virasoro repo's Python tools
"""Check agy's Lemma A1 (virasoro advice, item 1) against the repository's direct
Shapovalov computation of H_M.

Usage: python3 -u virasoro_lemmaA1.py [-h|--help] T_NUM T_DEN DELTA_NUM DELTA_DEN MMAX

With t = b^2 = T_NUM/T_DEN, c = 13 + 6(t + 1/t), d = h_{1,3}(b) = -1 - 2/t, and the
internal weight Delta = DELTA_NUM/DELTA_DEN, it computes for M = 0..MMAX
  * H_M from tools/direct_reconstruction.py (F_N = sum (G^-1) rho, then H = eta * F), and
  * the right side of Lemma A1: sum_k c_{M,k}(t) (-1)^k prod_{j=1}^{2k}(jt+2) /
    (2^k t^k prod_{j=1}^k (2 Delta - 2 h_{j,1}(t))),
    with c_{M,k} the coefficient of W^k q^M in prod_n (1 - q^n W/(1-q^n)^2)^{2/t},
and prints both and whether they agree exactly.
"""
import sys
from fractions import Fraction as Fr

if len(sys.argv) > 1 and sys.argv[1] in ("-h", "--help"):
    print(__doc__)
    sys.exit(0)
if len(sys.argv) != 6:
    print(__doc__)
    sys.exit(2)

tn, td, an, ad, MMAX = map(int, sys.argv[1:])
t = Fr(tn, td)
Delta = Fr(an, ad)
c = 13 + 6 * (t + 1 / t)
d = -1 - 2 / t

sys.path.insert(0, "/home/yang/virasoro/tools")
import direct_reconstruction as dr  # noqa: E402

dr.C_CHARGE = c
dr.set_external_weight(d)

# ---- direct H_M
F = []
for N in range(MMAX + 1):
    if N == 0:
        F.append(Fr(1))
        continue
    G = dr.mat_eval(dr.gram_matrix(N), Delta)
    R = dr.mat_eval(dr.vertex_matrix(N), Delta)
    det, tr = dr.det_and_trace_inv(G, R)
    assert det != 0, "Gram matrix singular at this Delta"
    F.append(tr)
eta = dr.euler_coeffs(MMAX) if hasattr(dr, "euler_coeffs") else None
# Euler coefficients of prod (1-q^m), computed here to be independent
e = [Fr(0)] * (MMAX + 1)
e[0] = Fr(1)
for m in range(1, MMAX + 1):
    new = e[:]
    for i in range(m, MMAX + 1):
        new[i] -= e[i - m]
    e = new
H = [sum(e[j] * F[N - j] for j in range(N + 1)) for N in range(MMAX + 1)]

# ---- Lemma A1 right side
gamma = 2 / t


def binom(g, j):
    r = Fr(1)
    for i in range(j):
        r = r * (g - i) / (i + 1)
    return r


# series in q (index M) with coefficients polynomials in W (dict k -> Fr)
def ser_mul(A, B):
    out = [dict() for _ in range(MMAX + 1)]
    for i, a in enumerate(A):
        if not a:
            continue
        for j in range(MMAX + 1 - i):
            b = B[j]
            for ka, va in a.items():
                for kb, vb in b.items():
                    out[i + j][ka + kb] = out[i + j].get(ka + kb, Fr(0)) + va * vb
    return out


def inv_one_minus_qn_sq_power(n, r):
    """(1-q^n)^(-2r) as a q-series (list of Fr), truncated at MMAX."""
    s = [Fr(0)] * (MMAX + 1)
    for j in range(0, MMAX // n + 1):
        s[j * n] = binom(Fr(-2 * r), j) * (-1) ** j
    return s


total = [dict() for _ in range(MMAX + 1)]
total[0][0] = Fr(1)
for n in range(1, MMAX + 1):
    # factor (1 - x)^gamma with x = q^n W / (1-q^n)^2 = sum_r binom(gamma,r)(-1)^r q^{nr} W^r (1-q^n)^{-2r}
    fac = [dict() for _ in range(MMAX + 1)]
    for r in range(0, MMAX // n + 1):
        coef = binom(gamma, r) * (-1) ** r
        s = inv_one_minus_qn_sq_power(n, r)
        for j, v in enumerate(s):
            if v and n * r + j <= MMAX:
                fac[n * r + j][r] = fac[n * r + j].get(r, Fr(0)) + coef * v
    total = ser_mul(total, fac)


def h_u1(u):
    return ((1 - u * u) * t + 2 * (1 - u)) / 4


def Lam(k):
    num = Fr((-1) ** k)
    for j in range(1, 2 * k + 1):
        num *= (j * t + 2)
    den = Fr(2) ** k * t ** k
    for j in range(1, k + 1):
        den *= (2 * Delta - 2 * h_u1(j))
    return num / den


ok_all = True
for M in range(MMAX + 1):
    rhs = sum(v * Lam(k) for k, v in total[M].items())
    ok = rhs == H[M]
    ok_all &= ok
    print(f"M={M}: direct H_M = {H[M]}   formula = {rhs}   {'AGREE' if ok else 'DIFFER'}", flush=True)
print("ALL AGREE" if ok_all else "MISMATCH")

# ---- step 4 of item 1: P_M(t,Y) as written by agy, against M! t^{2M} prod_u (2Delta-2h_{u,1}) * H_M
from math import factorial
Y = Delta * t * t
ok4 = True
for M in range(1, MMAX + 1):
    lhs = Fr(factorial(M)) * t ** (2 * M) * H[M]
    for u in range(1, M + 1):
        lhs *= (2 * Delta - 2 * h_u1(u))
    rhs = Fr(0)
    for k in range(1, M + 1):
        term = Fr(factorial(M), factorial(k)) * (-1) ** k * factorial(k) * t ** k * total[M].get(k, Fr(0))
        for i in range(1, k + 1):
            term *= (i * t + 1) * ((2 * i - 1) * t + 2)
        for u in range(k + 1, M + 1):
            term *= (2 * Y + (u - 1) * t * t + Fr(u * u - 1, 2) * t ** 3)
        rhs += term
    ok = lhs == rhs
    ok4 &= ok
    print(f"P_{M}: cleared H = {lhs}  agy step-4 formula = {rhs}  {'AGREE' if ok else 'DIFFER'}", flush=True)
print("STEP4 ALL AGREE" if ok4 else "STEP4 MISMATCH")
