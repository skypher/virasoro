"""Intermediate closed forms for the identities of sphere/paper.tex Lemma 3.5(i) (lem:saddle).

Variables s1 = sqrt(1-p), s2 = sqrt(1-y), s3 = sqrt(1-x).  Prints each term
of the three generating-function identities and the sum (expected 0).
Usage: python3 -u sphere/tools/check_saddle_identities.py   (no options; runs in seconds)
"""
import sys
import sympy as sp

if len(sys.argv) > 1 and sys.argv[1] in ("-h", "--help"):
    print(__doc__)
    sys.exit(0)

s1, s2, s3 = sp.symbols('s1 s2 s3', positive=True)
I = sp.I
p = 1 - s1**2
y = 1 - s2**2
x = 1 - s3**2


def A(s):
    return -2*I*(1/s - 1)


def B(sa, sb):
    pa = 1 - sa**2
    pb = 1 - sb**2
    return -pa*pb/(2*sa*sb*(sa + sb)**2)


def ydy(expr, s):
    """y d/dy with y = 1 - s^2, i.e. -(1-s^2)/(2s) d/ds."""
    return sp.simplify(-(1 - s**2)/(2*s)*sp.diff(expr, s))


e0 = sp.simplify(I*A(s1) - A(s1)**2/4 - p/(1 - p))
print('sigma^0 identity:', e0, flush=True)

T1 = sp.factor(sp.simplify((p*A(s2) - y*A(s1))/(y - p) - p/(1 - p)*A(s2)))
print('T1 =', T1)
print('y d/dy T1 =', sp.factor(ydy(T1, s2)))
print('(2i-A(p))B(p,y) =', sp.factor(sp.simplify((2*I - A(s1))*B(s1, s2))))
print('sigma^1 identity:', sp.simplify((2*I - A(s1))*B(s1, s2) + ydy(T1, s2)), flush=True)

T2a = sp.factor(sp.simplify((p*B(s2, s3) - y*B(s1, s3))/(y - p) - p/(1 - p)*B(s2, s3)))
T2b = sp.factor(sp.simplify((p*B(s2, s3) - x*B(s1, s2))/(x - p) - p/(1 - p)*B(s2, s3)))
print('T2a =', T2a)
print('T2b =', T2b)
print('y d/dy T2a =', sp.factor(ydy(T2a, s2)))
print('x d/dx T2b =', sp.factor(ydy(T2b, s3)))
print('B(p,y)B(p,x) =', sp.factor(B(s1, s2)*B(s1, s3)))
print('sigma^2 identity:', sp.simplify(ydy(T2a, s2) + ydy(T2b, s3) - B(s1, s2)*B(s1, s3)), flush=True)
