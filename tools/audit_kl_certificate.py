#!/usr/bin/env python3
"""Exact certificate for Corollary cor:top-layer-sharp: for 2 <= M <= MMAX, at every minimal-model
charge, dH_M/dd at d = 0 and at d = 1 (Lemma lem:d-derivatives) never vanish together at a weight
that is not a Kac weight of level <= M.

Usage: python3 -u tools/audit_kl_certificate.py [MMAX] [-h|--help]   (default MMAX = 40, ~20 min)

Variables t = b^2 and w = 4 t h - (t+1)^2, so that h - h_{r,s} = (w + (rt+s)^2)/(4t).  Up to nonzero
factors (t != 0, +-1), the two derivatives are
  K_M = sum_{rs=M} (rt+s)/(w + (rt+s)^2),   L_M = sum_{rs=M} (rt-s)/(w + (rt+s)^2).
With NK, NL their numerators over prod_{rs=M}(w + (rt+s)^2), the script checks that NK, NL are
coprime, factors the resultant Res_w(NK, NL) over Q, and for every irreducible factor f(t) other
than t, t-1, t+1 forms the ideal (NK, NL, f) and reduces the product of the Kac factors
w + (r't+s')^2, r's' <= M (or its square or cube) modulo it.  A factor passes if the product
reduces to 0 (all common zeros on it are Kac weights) or if f has no root t = -p'/p with p, p' >= 2
coprime (minimal-model charges); irreducible factors of degree >= 2 have no rational roots.
"""

import sys
import time

if any(a in ("-h", "--help") for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)

import sympy as sp  # noqa: E402

t, w = sp.symbols("t w")
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
t0 = time.time()
failures = 0
for m in range(2, MMAX + 1):
    labels = [(r, m // r) for r in range(1, m + 1) if m % r == 0]
    ks = [w + (r * t + s) ** 2 for r, s in labels]
    nk = sp.expand(sum((r * t + s) * sp.prod([ks[j] for j in range(len(labels)) if j != i])
                       for i, (r, s) in enumerate(labels)))
    nl = sp.expand(sum((r * t - s) * sp.prod([ks[j] for j in range(len(labels)) if j != i])
                       for i, (r, s) in enumerate(labels)))
    coprime = sp.Poly(sp.gcd(nk, nl), w, t).total_degree() == 0
    res = sp.resultant(nk, nl, w)
    kac = [w + (r2 * t + n // r2) ** 2 for n in range(1, m + 1)
           for r2 in range(1, n + 1) if n % r2 == 0]
    bad = []
    for f, _ in sp.factor_list(sp.Poly(res, t))[1]:
        fe = f.as_expr()
        if f.degree() == 0 or fe in (t, t - 1, t + 1, 1 - t):
            continue
        G = sp.groebner([nk, nl, fe], w, t, order="lex", domain="QQ")
        if list(G) == [1]:
            continue
        killed = False
        for e in (1, 2, 3):
            acc = sp.Integer(1)
            for k in kac:
                acc = G.reduce(sp.expand(acc * k ** e))[1]
                if acc == 0:
                    break
            if acc == 0:
                killed = True
                break
        if killed:
            continue
        if f.degree() == 1:
            root = sp.Rational(-f.all_coeffs()[1], f.all_coeffs()[0])
            if root < 0 and root.p != -1 and root.q != 1:
                bad.append(root)
    ok = coprime and not bad and res != 0
    failures += not ok
    print(("PASS" if ok else "FAIL") + f" M={m}: coprime {coprime}, minimal-model "
          f"non-Kac common zeros {bad} ({time.time() - t0:.0f}s)", flush=True)

if failures:
    print(f"{failures} FAILURES", flush=True)
    sys.exit(1)
print("ALL PASS", flush=True)
