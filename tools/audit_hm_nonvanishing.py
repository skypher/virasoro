#!/usr/bin/env python3
"""Exact certificate: H_M(c,h,.) is not identically zero in d at nondegenerate (c,h), for M <= MMAX.

Usage: python3 -u tools/audit_hm_nonvanishing.py [MMAX] [-h|--help]   (default MMAX = 5)

For each M, H_M(c,h,d) = sum_j eta_j F_{M-j} is written over the common denominator
prod_{M'<=M} det G_{M'}(c,h); its numerator is d(d-1) times a polynomial in d whose coefficients
lie in Q[c,h].  With g their gcd and I the ideal of the coefficients divided by g, the script
checks that every prime factor of g divides some det G_{M'} (M' <= M), and that a power of
prod_{M'<=M} det G_{M'} lies in I (Groebner-basis reduction over Q).  Together these show that
the coefficients vanish simultaneously only where some det G_{M'}(c,h) = 0, which is the
statement used in Corollary cor:top-layer-sharp.  MMAX = 5 takes about 17 minutes.
"""

import sys
import time

if any(a in ("-h", "--help") for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import sympy as sp  # noqa: E402

from exact_shapovalov import (  # noqa: E402
    c,
    d,
    euler_coefficients,
    gram_entry,
    h,
    partitions,
    vertex_entry,
)

MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
t0 = time.time()
failures = 0
nums, dets = {}, {}
for level in range(1, MMAX + 1):
    basis = list(partitions(level))
    gram = sp.Matrix([[gram_entry(a, b) for b in basis] for a in basis])
    rho = sp.Matrix([[vertex_entry(a, b) for b in basis] for a in basis])
    dets[level] = sp.expand(gram.det(method="berkowitz"))
    adj = gram.adjugate(method="berkowitz")
    nums[level] = sp.expand(sum(adj[i, j] * rho[j, i]
                                for i in range(len(basis)) for j in range(len(basis))))
    print(f"level {level}: adjugate trace done ({time.time() - t0:.0f}s)", flush=True)

for m in range(1, MMAX + 1):
    eta = euler_coefficients(m)
    expr = sum(eta[j] * (nums[m - j] / dets[m - j] if m - j > 0 else 1) for j in range(m + 1))
    num, _ = sp.fraction(sp.together(expr))
    poly = sp.Poly(sp.expand(num), d)
    quot, rem = sp.div(poly, sp.Poly(d * (d - 1), d))
    assert rem.is_zero
    coeffs = [sp.expand(x) for x in quot.all_coeffs()]
    g = coeffs[0]
    for x in coeffs[1:]:
        g = sp.gcd(g, x)
    det_factors = set()
    for level in range(1, m + 1):
        for f, _ in sp.factor_list(dets[level])[1]:
            det_factors.add(sp.Poly(f, c, h).monic().as_expr())
    g_ok = all(sp.Poly(f, c, h).monic().as_expr() in det_factors or sp.Poly(f, c, h).total_degree() == 0
               for f, _ in sp.factor_list(g)[1])
    reduced = [sp.cancel(x / g) for x in coeffs]
    gb = sp.groebner(reduced, c, h, order="grevlex")
    prod = sp.expand(sp.prod([dets[level] for level in range(1, m + 1)]))
    member = None
    for e in range(1, 6):
        _, r = gb.reduce(sp.expand(prod ** e))
        if r == 0:
            member = e
            break
    ok = g_ok and member is not None
    failures += not ok
    print(("PASS" if ok else "FAIL")
          + f" M={m}: gcd factors are Kac factors: {g_ok}; (prod det G)^{member} in the "
          f"coefficient ideal ({time.time() - t0:.0f}s)", flush=True)

if failures:
    print(f"{failures} FAILURES", flush=True)
    sys.exit(1)
print("ALL PASS", flush=True)
