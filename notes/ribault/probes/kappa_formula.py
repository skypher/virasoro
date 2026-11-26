"""Usage: python3 -u kappa_formula.py [--logs kappa_23.log,...]
       python3 -u kappa_formula.py -h | --help

Compare the measured top-coefficient ratios kappa(lambda,nu,mu) (kappa_probe.py logs) with the
closed formula from the first-step Vandermonde argument.  Signed node momenta (layer 0 = lambda):
  S0 = n0, S^+_{2j} = n0 + j N0, S^-_{2j} = n0 - j N0, S^+_{2j+1} = n1 + j N0,
  S^-_{2j+1} = n1 - (j+1) N0,  N0 = 2pp'.
First steps from a toward b: FS(a,b) = nodes c at odd relative layer from a with layer(c) < layer(b),
plus b itself if layer(b) - layer(a) is odd.  For c at odd relative layer from a,
  kappa(a,c,b) = (x_c/x_a)^(L_b - L_c) prod_{c' in FS(c,b)} (x_c' - x_a)
                 / prod_{c~ in FS(a,b) minus FS(a,c)} (x_c~ - x_c),
and for nu at even relative layer, kappa(a,nu,b) = kappa(c,nu,b) kappa(a,c,b) / kappa(a,c,nu) with c a
node of layer L_a + 1.
"""
# py-rules-ok: case a, parses logs and evaluates rational products, instant
import argparse
import os
import re
from fractions import Fraction as Fr


def S(n0, n1, N0, node):
    L, sg = node
    if L == 0:
        return n0
    if L % 2 == 0:
        j = L // 2
        return n0 + j * N0 if sg == "+" else n0 - j * N0
    j = (L - 1) // 2
    return n1 + j * N0 if sg == "+" else n1 - (j + 1) * N0


def layer_nodes(L):
    return [(L, "0")] if L == 0 else [(L, "+"), (L, "-")]


def FS(a, b):
    La, Lb = a[0], b[0]
    out = []
    for L in range(La + 1, Lb, 2):
        out += layer_nodes(L)
    if (Lb - La) % 2 == 1:
        out.append(b)
    return out


def kappa_odd(x, a, c, b):
    num = Fr(x(c), x(a)) ** (b[0] - c[0])
    for cp in FS(c, b):
        num *= (x(cp) - x(a))
    den = Fr(1)
    fsac = set(FS(a, c))
    for ct in FS(a, b):
        if ct not in fsac:
            den *= (x(ct) - x(c))
    return num / den


def kappa(x, a, nu, b):
    if (nu[0] - a[0]) % 2 == 1:
        return kappa_odd(x, a, nu, b)
    c = (a[0] + 1, "+")
    return kappa_odd(x, c, nu, b) * kappa_odd(x, a, c, b) / kappa_odd(x, a, c, nu)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--logs", default="kappa_23.log,kappa_25.log,kappa_34.log,kappa_27.log,kappa_35.log,kappa_45.log,kappa_23_L5.log,kappa_25_L4.log")
    a = ap.parse_args()
    ok = bad = 0
    for f in a.logs.split(","):
        cur = None
        for line in open(os.path.join(here, f)):
            m = re.match(r"\((\d+),(\d+)\) \(r,s\)=\((\d+),(\d+)\) n0=(-?\d+)", line)
            if m:
                p, pp, r, s, n0 = map(int, m.groups())
                cur = (n0, pp * r + p * s, 2 * p * pp)
                continue
            m = re.search(r"kappa\(lambda, (\d)(.) \[m=(-?\d+)\], (\d)(.) \[m=(-?\d+)\]\) = (\S+)", line)
            if m and cur:
                La, sa, _, Lb, sb, _, k = m.groups()
                n0, n1, N0 = cur
                x = lambda node: S(n0, n1, N0, node)  # noqa: E731
                pred = kappa(x, (0, "0"), (int(La), sa), (int(Lb), sb))
                if pred == Fr(k):
                    ok += 1
                else:
                    bad += 1
                    print(f"MISMATCH {f}: {line.strip()} predicted {pred}", flush=True)
    print(f"kappa formula: {ok} agree, {bad} disagree", flush=True)


if __name__ == "__main__":
    main()
