"""Intermediate closed forms for the sigma^1 identities of sphere/paper.tex Lemma 3.7 (lem:ext-exponents),
and the numerator identity of the sigma^2 part of Lemma 3.5(i).

s1 = sqrt(1-p), s2 = sqrt(1-y), s3 = sqrt(1-x).
Usage: python3 -u sphere/tools/check_ext_exponent_identities.py   (no options; runs in seconds)
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


def B(sa, sb):
    pa = 1 - sa**2
    pb = 1 - sb**2
    return -pa*pb/(2*sa*sb*(sa + sb)**2)


def ydy(expr, s):
    return sp.simplify(-(1 - s**2)/(2*s)*sp.diff(expr, s))


def Cp(s):
    return I/2*(1 - s**2)/s**3


def Cm(s):
    return -I/2*(1 - s**2)/s


for name, C, rhs in (('C+', Cp, p/(2*(1 - p)**2)*Cp(s2)), ('C-', Cm, -p/(2*(1 - p))*Cm(s2))):
    T = sp.factor(sp.simplify((p*C(s2) - y*C(s1))/(y - p) - p/(1 - p)*C(s2)))
    print(name, 'T =', T)
    dT = sp.factor(ydy(T, s2))
    print(name, 'y d/dy T =', dT)
    BC = sp.factor(sp.simplify(B(s1, s2)*C(s1)))
    print(name, 'B(p,y)C(p) =', BC)
    print(name, 'rhs =', sp.factor(rhs))
    print(name, 'identity:', sp.simplify(dT - BC - rhs), flush=True)

# Lemma 3.5(i), sigma^2: numerators over 4 s1^2 s2 s3 (s1+s2)^2 (s1+s3)^2 (s2+s3)^3,
# after the prefactor -pxy.
den = 4*s1**2*s2*s3*(s1 + s2)**2*(s1 + s3)**2*(s2 + s3)**3


def T2(sa, sb, sc):
    pa = 1 - sa**2
    pb = 1 - sb**2
    return (pa*B(sb, sc) - pb*B(sa, sc))/(pb - pa) - pa/(1 - pa)*B(sb, sc)


Na = sp.expand(sp.cancel(ydy(T2(s1, s2, s3), s2)*den/(-p*x*y)))
Nb = sp.expand(sp.cancel(ydy(T2(s1, s3, s2), s3)*den/(-p*x*y)))
print('Na =', sp.factor(Na))
print('Nb =', sp.factor(Nb))
print('Na+Nb =', sp.factor(Na + Nb))
print('check Na+Nb = (s1^2-1)(s2+s3)^3:', sp.expand(Na + Nb - (s1**2 - 1)*(s2 + s3)**3) == 0, flush=True)
