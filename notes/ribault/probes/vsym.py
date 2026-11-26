"""Usage: python3 -u vsym.py [--L LMAX]
       python3 -u vsym.py -h | --help

Solve the leading-order cutting recursion
   j v^(k)_j(a,b) = v^(k+1)_{j-1}(a,b) - sum_{nu at layer L_a + k} kappa(a,nu,b) v^(1)_{j-1}(nu,b),
   v^(D)_0 = 1   (k + j = D = L_b - L_a, v = c(b*)/Top(a->b)),
symbolically in n0, n1, N0 with the closed kappa of kappa_formula.py, and print v^(k)_j(lambda,mu)
divided by z^j, z = S_mu/S_lambda (signed momenta), for every end node mu up to layer LMAX.
"""
# py-rules-ok: case a, sympy on at most a few hundred rational functions, seconds
import argparse
from functools import lru_cache
import sympy as sp

n0, n1, N0 = sp.symbols("n0 n1 N0")


def S(node):
    L, sg = node
    if L == 0:
        return n0
    if L % 2 == 0:
        j = L // 2
        return n0 + j * N0 if sg == "+" else n0 - j * N0
    j = (L - 1) // 2
    return n1 + j * N0 if sg == "+" else n1 - (j + 1) * N0


def layer_nodes(L):
    return [(0, "0")] if L == 0 else [(L, "+"), (L, "-")]


def FS(a, b):
    out = []
    for L in range(a[0] + 1, b[0], 2):
        out += layer_nodes(L)
    if (b[0] - a[0]) % 2 == 1:
        out.append(b)
    return out


def kappa_odd(a, c, b):
    num = (S(c) / S(a)) ** (b[0] - c[0])
    for cp in FS(c, b):
        num *= (S(cp) - S(a))
    den = 1
    fsac = set(FS(a, c))
    for ct in FS(a, b):
        if ct not in fsac:
            den *= (S(ct) - S(c))
    return num / den


def kappa(a, nu, b):
    if (nu[0] - a[0]) % 2 == 1:
        return kappa_odd(a, nu, b)
    c = (a[0] + 1, "+")
    return kappa_odd(c, nu, b) * kappa_odd(a, c, b) / kappa_odd(a, c, nu)


@lru_cache(maxsize=None)
def v(a, b, k, j):
    D = b[0] - a[0]
    assert k + j == D and k >= 1
    if j == 0:
        return sp.Integer(1)
    out = v(a, b, k + 1, j - 1)
    for nu in layer_nodes(a[0] + k):
        out -= kappa(a, nu, b) * v(nu, b, 1, j - 1)
    return sp.factor(sp.together(out / j))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--L", type=int, default=5)
    a = ap.parse_args()
    lam = (0, "0")
    for L in range(1, a.L + 1):
        for mu in layer_nodes(L):
            z = S(mu) / S(lam)
            row = [sp.factor(sp.simplify(v(lam, mu, L - j, j) / z ** j)) for j in range(L)]
            print(f"L={L} mu={mu}: v/z^j = {row}", flush=True)


if __name__ == "__main__":
    main()
