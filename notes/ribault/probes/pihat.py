"""Usage: python3 -u pihat.py [--D DMAX] [--show]
       python3 -u pihat.py -h | --help

Normalized two-variable resolvent of the leading chain sums (notes/ribault/subleading.tex, Section on
k + j = L).  Nodes are positions pi in (1/2)Z (layer 2|pi|), S(pi) = alpha + pi for integer pi and
beta + pi otherwise (N0 = 1).  For a base a and end mu, Pi_a(s,t) is the polynomial of degree <= D-1
in s (D = layer(mu) - layer(a)) with
  Pi_a(S_theta, t) = Pi_theta(S_a, t) * prod_{eta in LS(a->mu) - LS(theta->mu)} (t - S_eta),
       theta in FS(a->mu), theta != mu,
  Pi_a(S_mu, t)    = prod_{eta in LS(a->mu), eta != a} (t - S_eta)      (D odd).
Prints, for base pi = 0 and each end mu, the total degree, the top-degree part (claimed
sum_j mu_j(D) s^j t^(D-1-j)) and with --show the whole polynomial.
"""
# py-rules-ok: case a, sympy interpolation over at most ~2*DMAX nodes per base, seconds to a minute
import argparse
from fractions import Fraction as Fr
from functools import lru_cache
import sympy as sp

al, be, s, t = sp.symbols("alpha beta s t")
HALF = Fr(1, 2)


def cls(p):
    return p.denominator == 1  # True: integer class


def S(p):
    return (al if cls(p) else be) + sp.Rational(p.numerator, p.denominator)


def nodes_between(lo, hi, klass):
    """positions with lo < |pi| < hi of the given class (True = integer)."""
    out = []
    x = Fr(0) if klass else HALF
    while x < hi:
        if x > lo:
            out += [x] if x == 0 else [x, -x]
        x += 1
    return out


def FS(a, mu):
    out = nodes_between(abs(a), abs(mu), not cls(a))
    if cls(mu) != cls(a):
        out.append(mu)
    return out


def LS(a, mu):
    out = nodes_between(abs(a), abs(mu), not cls(mu))
    if cls(a) != cls(mu):
        out.append(a)
    return out


@lru_cache(maxsize=None)
def Pi(a, mu):
    D = int(2 * (abs(mu) - abs(a)))
    pts, vals = [], []
    lsa = LS(a, mu)
    for th in FS(a, mu):
        if th == mu:
            v = sp.Integer(1)
            for e in lsa:
                if e != a:
                    v *= (t - S(e))
        else:
            lst = set(LS(th, mu))
            v = Pi(th, mu).subs(s, S(a))
            for e in lsa:
                if e not in lst:
                    v *= (t - S(e))
        pts.append(S(th))
        vals.append(sp.expand(v))
    assert len(pts) == D, (a, mu, len(pts), D)
    poly = 0
    for i, (x, v) in enumerate(zip(pts, vals)):
        term = v
        for k, y in enumerate(pts):
            if k != i:
                term *= (s - y) / (x - y)
        poly += term
    return sp.expand(sp.simplify(poly))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--D", type=int, default=5)
    ap.add_argument("--show", action="store_true")
    a = ap.parse_args()
    for D in range(1, a.D + 1):
        for sg in (1, -1):
            mu = sg * Fr(D, 2)
            P = sp.Poly(Pi(Fr(0), mu), s, t)
            deg = P.total_degree()
            top = sum(c * s ** m[0] * t ** m[1] for m, c in P.terms() if m[0] + m[1] == deg)
            print(f"D={D} mu={mu}: total degree {deg}; top part {sp.factor(top)}", flush=True)
            if a.show:
                print(f"   Pi = {sp.factor(P.as_expr())}", flush=True)


if __name__ == "__main__":
    main()
