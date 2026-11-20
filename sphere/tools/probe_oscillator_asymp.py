#!/usr/bin/env python3
"""Probe the exact large-lambda (large-Delta) oscillator expansion of the sphere 4-point block.

Solves eq. (feqn) of Besken-Datta-Kraus (arXiv:1910.04169) perturbatively in 1/lambda:
  F(sigma) = exp(lambda^2 S0(sigma) + lambda S1(sigma) + S2(sigma) + O(1/lambda))
to check whether S1(sigma) and S2(sigma) truncate in oscillator degree and admit
closed-form generating functions.
"""

from __future__ import annotations

import argparse
from itertools import combinations_with_replacement
import sympy as sp


def partitions(n: int, largest: int | None = None):
    if n == 0:
        yield ()
        return
    if largest is None or largest > n:
        largest = n
    for first in range(largest, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def main():
    parser = argparse.ArgumentParser(description="Probe S0, S1, S2 in the large-Delta oscillator expansion.")
    parser.add_argument("--max-level", type=int, default=5, help="Max oscillator level (default: 5)")
    args = parser.parse_args()
    N = args.max_level

    mu, h1, h2 = sp.symbols("mu h1 h2")
    I = sp.I
    # Variables sigma_1 .. sigma_N
    sig = {m: sp.Symbol(f"s{m}") for m in range(1, N + 1)}

    # Exact A_m and B_{m,n} from generating functions:
    # A(p) = -2i ((1-p)^{-1/2} - 1)
    # B(p,q) = -1/2 p q ((1-p)(1-q))^{-1/2} ((1-p)^{1/2} + (1-q)^{1/2})^{-2}
    p, q = sp.symbols("p q")
    A_ser = sp.series(-2 * I * ((1 - p) ** (-sp.Rational(1, 2)) - 1), p, 0, N + 1).removeO()
    A = {m: sp.expand(A_ser.coeff(p, m)) for m in range(1, N + 1)}

    B_expr = -sp.Rational(1, 2) * p * q * ((1 - p) * (1 - q)) ** (-sp.Rational(1, 2)) * (
        (1 - p) ** sp.Rational(1, 2) + (1 - q) ** sp.Rational(1, 2)
    ) ** (-2)
    B_ser_p = sp.series(B_expr, p, 0, N + 1).removeO()
    B = {}
    for m in range(1, N + 1):
        cm = sp.series(B_ser_p.coeff(p, m), q, 0, N + 1 - m).removeO()
        for n in range(1, N + 1 - m):
            B[(m, n)] = sp.expand(cm.coeff(q, n))

    S0 = sum(A[m] * sig[m] for m in range(1, N + 1)) + sum(
        B[(m, n)] * sig[m] * sig[n] for m in range(1, N + 1) for n in range(1, N + 1 - m)
    )

    def L0_op(k: int, expr):
        """Linear operator L_k^(0) acting on polynomial in s_1..s_N (valid up to level N-k)."""
        res = I * sp.diff(expr, sig[k])
        for n in range(1, N - k + 1):
            res += n * sig[n] * (sp.diff(expr, sig[n + k]) - sp.diff(expr, sig[n]))
        for n in range(1, k):
            res -= sp.Rational(1, 2) * sp.diff(S0, sig[n]) * sp.diff(expr, sig[k - n])
        return sp.expand(res)

    def trunc_level(expr, max_lvl):
        """Keep only monomials of weight <= max_lvl."""
        poly = sp.Poly(expr, *[sig[m] for m in range(1, N + 1)])
        out = sp.Integer(0)
        for monom, coeff in poly.terms():
            lvl = sum((idx + 1) * exp for idx, exp in enumerate(monom))
            if lvl <= max_lvl:
                term = coeff
                for idx, exp in enumerate(monom):
                    if exp:
                        term *= sig[idx + 1] ** exp
                out += term
        return sp.expand(out)

    # Solve for S1 level by level: L_k^(0)(S1) + mu * k * d_k(S0) = 0
    # Monomials of level m are indexed by partitions of m
    S1_coeffs = {}
    S1_expr = sp.Integer(0)
    for lvl in range(1, N + 1):
        parts = list(partitions(lvl))
        unknowns = [sp.Symbol(f"c1_{lvl}_{i}") for i in range(len(parts))]
        chunk = sum(u * sp.prod(sig[x] for x in P) for u, P in zip(unknowns, parts))
        cand = S1_expr + chunk
        eqs = []
        for k in range(1, lvl + 1):
            lhs = L0_op(k, cand) + mu * k * sp.diff(S0, sig[k])
            # Extract monomials of level (lvl - k)
            poly = sp.Poly(lhs, *[sig[m] for m in range(1, N + 1)])
            for monom, coeff in poly.terms():
                mlvl = sum((idx + 1) * exp for idx, exp in enumerate(monom))
                if mlvl == lvl - k:
                    eqs.append(sp.expand(coeff))
        sol = sp.solve(eqs, unknowns)
        assert len(sol) == len(unknowns), f"S1 solve failed at level {lvl}: {sol}"
        for P, u in zip(parts, unknowns):
            val = sp.simplify(sol[u])
            if val != 0:
                S1_coeffs[P] = val
        S1_expr = sp.expand(cand.subs(sol))

    print("=== S1(sigma) coefficients ===", flush=True)
    for P, val in sorted(S1_coeffs.items(), key=lambda kv: (sum(kv[0]), len(kv[0]), kv[0])):
        print(f"  {P}: {val}", flush=True)

    # Solve for S2 level by level:
    # L_k^(0)(S2) - 1/4 sum_{n=1}^{k-1} d_n(S1)*d_{k-n}(S1) + mu*k*d_k(S1) + (h2 - 1/16) - k*(h1 - 1/16) - mu^2 = 0
    # Wait: check sign of -1/4 sum d_n d_{k-n} S0: we already know -1/4 sum d_n d_{k-n} S0 = +(k-1)/16!
    # Double check directly!
    for k in range(1, N + 1):
        d2 = sum(sp.diff(S0, sig[n], sig[k - n]) for n in range(1, k))
        check = sp.simplify(-sp.Rational(1, 4) * d2 - sp.Rational(k - 1, 16))
        assert check == 0, f"S0 second derivative check failed at k={k}: {check}"
    print("[PASS] Verified -1/4 sum d_n d_{k-n} S0 == (k-1)/16 for k=1..N", flush=True)

    S2_coeffs = {}
    S2_expr = sp.Integer(0)
    for lvl in range(1, N + 1):
        parts = list(partitions(lvl))
        unknowns = [sp.Symbol(f"c2_{lvl}_{i}") for i in range(len(parts))]
        chunk = sum(u * sp.prod(sig[x] for x in P) for u, P in zip(unknowns, parts))
        cand = S2_expr + chunk
        eqs = []
        for k in range(1, lvl + 1):
            src = (
                -sp.Rational(1, 4) * sum(sp.diff(S1_expr, sig[n]) * sp.diff(S1_expr, sig[k - n]) for n in range(1, k))
                + mu * k * sp.diff(S1_expr, sig[k])
                + (h2 - sp.Rational(1, 16))
                - k * (h1 - sp.Rational(1, 16))
                - mu**2
            )
            lhs = L0_op(k, cand) + src
            poly = sp.Poly(lhs, *[sig[m] for m in range(1, N + 1)])
            for monom, coeff in poly.terms():
                mlvl = sum((idx + 1) * exp for idx, exp in enumerate(monom))
                if mlvl == lvl - k:
                    eqs.append(sp.expand(coeff))
        sol = sp.solve(eqs, unknowns)
        assert len(sol) == len(unknowns), f"S2 solve failed at level {lvl}: {sol}"
        for P, u in zip(parts, unknowns):
            val = sp.simplify(sol[u])
            if val != 0:
                S2_coeffs[P] = val
        S2_expr = sp.expand(cand.subs(sol))

    print("\n=== S2(sigma) coefficients ===", flush=True)
    for P, val in sorted(S2_coeffs.items(), key=lambda kv: (sum(kv[0]), len(kv[0]), kv[0])):
        print(f"  {P}: {sp.factor(val)}", flush=True)


if __name__ == "__main__":
    main()
