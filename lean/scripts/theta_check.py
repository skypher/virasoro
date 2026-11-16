"""Check T = A_k A_t P_k P_t ((sig_k + sig_t)/c + 3e/(4c^2)) against the paper's Theta7, Theta10.

Usage: python3 -u theta_check.py [-h|--help]
"""
import sys
if any(a in ('-h', '--help') for a in sys.argv[1:]):
    print(__doc__)
    sys.exit(0)
import sympy as sp

d = sp.symbols('d')
R = sp.Rational


def genAIndex(r, s):
    return [(p, q) for p in range(1 - r, r + 1) for q in range(1 - s, s + 1)
            if (p, q) != (0, 0) and (p, q) != (r, s)]


def lam(n):
    return R(n * n - 1, 48)


def A(r, s):
    idx = genAIndex(r, s)
    n = len(idx)
    assert n % 2 == 0
    val = R(1, 2) * R(-3, 4) ** (n // 2)
    for p, q in idx:
        val *= R(4, 4 * p - 3 * q)
    return val


def odds(n):
    return [k for k in range(2 * n) if k % 2 == 1]


def P(r, s):
    v = 1
    for k in odds(r):
        for l in odds(s):
            v *= (lam(abs(4 * k - 3 * l)) - d) * (lam(4 * k + 3 * l) - d)
    return sp.expand(v)


def sig(r, s):
    sA = sum(R(3, 4) * R(4 * p + 3 * q, 4 * p - 3 * q) for p, q in genAIndex(r, s))
    sP = sum(R(7 - 16 * k * k + 9 * l * l, 32) * (1 / (lam(abs(4 * k - 3 * l)) - d)
                                                   + 1 / (lam(4 * k + 3 * l) - d))
             for k in odds(r) for l in odds(s))
    return sA + sP


def hD(r, s):
    return R(7 - 16 * r * r + 9 * s * s, 32)


def hE(r, s):
    return (R(1 - r * r) + R(27 * (1 - s * s), 16)) / 4


def T(k, t):
    c = hD(*k) - hD(*t)
    e = hE(*k) - hE(*t)
    return A(*k) * A(*t) * P(*k) * P(*t) * ((sig(*k) + sig(*t)) / c + 3 * e / (4 * c * c))


if __name__ == "__main__":
    print('A21', A(2, 1), 'A15', A(1, 5), 'A13', A(1, 3), 'A41', A(4, 1), flush=True)
    th7 = sp.factor(sp.together(T((2, 1), (1, 5)) + T((1, 3), (4, 1))))
    paper7 = -(d**2 * (d - 1)**2 * (2*d - 15) * (2*d - 7) * (2*d - 5) * (2*d - 1) * (3*d - 14)
               * (3*d - 5) / 2164322160000) * (84001*d**4 - 3376370*d**3 + 44478887*d**2
                                                - 209562838*d + 205096320)
    print('Theta7 matches paper:', sp.simplify(th7 - paper7) == 0, flush=True)
    th10 = sp.factor(sp.together(T((1, 2), (4, 2)) + T((2, 2), (1, 6))))
    paper10 = -(d**2 * (d - 1)**2 * (2*d - 7)**2 * (2*d - 1)**2 * (3*d - 14) * (3*d - 5)
                * (6*d - 55) * (6*d - 1) / 552735279561465000000) * (
        424640464*d**8 - 41506307104*d**7 + 1664502727528*d**6 - 35552058801520*d**5
        + 438148123547677*d**4 - 3142854705332170*d**3 + 12488401942129875*d**2
        - 23870935242348750*d + 14566042731240000)
    print('Theta10 matches paper:', sp.simplify(th10 - paper10) == 0, flush=True)
