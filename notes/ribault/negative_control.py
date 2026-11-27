#!/usr/bin/env python3
"""Negative control for jet_expansion.py: perturb one residue R_{r,s}(u) by a
factor (1 + eps*u) and check that b-derivative jets then survive.

Usage: python3 -u negative_control.py [--label 1,4] [--eps 1] [--nmax 8]
       python3 -u negative_control.py -h | --help
"""
import argparse
import sys
from fractions import Fraction as Fr

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "..", "tools", "fixed_charge"))
from layer2_recursion import Model, Ser, ser_mul, ser_add, ser_const, log  # noqa: E402
from jet_expansion import Jets  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--label", default="1,4")
    ap.add_argument("--eps", default="1")
    ap.add_argument("--nmax", type=int, default=8)
    ap.add_argument("--const", action="store_true",
                    help="scale R by the constant (1+eps) instead of (1+eps*u)")
    args = ap.parse_args()
    lab = tuple(int(x) for x in args.label.split(","))
    eps = Fr(args.eps)

    m = Model(2, 3, Fr(3, 7), 24)
    orig_R = m.R

    def R(r, s):
        ser = orig_R(r, s)
        if (r, s) == lab:
            if args.const:
                ser = ser_mul(ser, ser_const(1 + eps, m.prec))
            else:
                ser = ser_mul(ser, ser_add(ser_const(1, m.prec), Ser(1, [eps], m.prec)))
        return ser
    m.R = R
    J = Jets(m, 5)
    for N in range(5, args.nmax + 1):
        co = J.moment(Fr(0), 1, N)
        surv = {k: v for k, v in co.items() if k[0] != "one" and k[2] >= 1 and v != 0}
        log(f"perturbed R{lab}: N={N} k=1 surviving b-jets: "
            + (", ".join(f"d_u^{k[2]} d_D^{k[3]} H_{k[0]}@{k[1]}" for k in sorted(surv)) or "none"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
