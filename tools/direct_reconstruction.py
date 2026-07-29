#!/usr/bin/env python3
"""Exact reconstruction of torus one-point coefficients at c = 1/2.

Implements Virasoro Shapovalov (Gram) matrices and torus one-point (Ward)
matrices independently of exact_shapovalov.py, with the internal weight h
kept as an exact univariate polynomial (Fraction coefficients) and the
external weight d fixed to an exact rational.  F_N(h) = tr(G_N^{-1} rho_N^T)
is reconstructed exactly as a rational function of h by sampling and
interpolation, so that Laurent expansions at collision points can be
compared against the closed formulas of the paper.  Everything is exact
rational arithmetic; no floats, no sympy.

Conventions (matching the paper):
  [L_m, L_n] = (m-n) L_{m+n} + (c/12)(m^3-m) delta_{m+n,0},  c = 1/2.
  Verma basis at level N: L_{-Y}|h> for partitions Y (weakly decreasing),
  ordered as partitions(N) descending-lexicographic (largest first part first).
  Gram: G_{Y,Y'} = <h| L_{y_l}...L_{y_1} L_{-Y'} |h>.
  Vertex: rho_{Y,Y'} = <h| L_{y_l}...L_{y_1} V_d(1) L_{-Y'} |h>,
  with [L_n, V_d(z)] = z^n (z d/dz + (n+1) d) V_d(z), <h|V_d(z)|h> = z^-d.
"""

from fractions import Fraction as Fr
from functools import lru_cache

C_CHARGE = Fr(1, 2)

# ---------------------------------------------------------------- polynomials
# poly in h: tuple of Fractions, index = degree, normalized (no trailing zeros)

def pnorm(t):
    t = list(t)
    while t and t[-1] == 0:
        t.pop()
    return tuple(t)

def padd(a, b):
    n = max(len(a), len(b))
    return pnorm([ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                   for i in range(n) ])

def pmul(a, b):
    if not a or not b:
        return ()
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return pnorm(out)

def pscale(a, s):
    if s == 0:
        return ()
    return pnorm([x * s for x in a])

def peval(a, v):
    r = Fr(0)
    for coef in reversed(a):
        r = r * v + coef
    return r

PONE = (Fr(1),)
PH = (Fr(0), Fr(1))  # the polynomial h

# ------------------------------------------------------------------ partitions

def partitions(n, largest=None):
    if n == 0:
        yield ()
        return
    if largest is None or largest > n:
        largest = n
    for first in range(largest, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest

# ------------------------------------------------- normal ordering (negatives)
# words are tuples of negative ints, normal-ordered means ascending (-4,-2,-1)

@lru_cache(maxsize=None)
def normal_order(word):
    for i in range(len(word) - 1):
        a, b = word[i], word[i + 1]
        if a > b:  # e.g. (-1,-2): swap plus commutator (a-b) L_{a+b}
            out = {}
            for w, coef in normal_order(word[:i] + (b, a) + word[i + 2:]).items():
                out[w] = out.get(w, Fr(0)) + coef
            for w, coef in normal_order(word[:i] + (a + b,) + word[i + 2:]).items():
                out[w] = out.get(w, Fr(0)) + (a - b) * coef
            return {w: c for w, c in out.items() if c != 0}
    return {word: Fr(1)}

# ------------------------------------------------- action of L_m, m>0, on word
# returns dict word -> poly in h

def _dadd(target, word, poly):
    if poly:
        cur = target.get(word)
        target[word] = padd(cur, poly) if cur is not None else poly
        if not target[word]:
            del target[word]

@lru_cache(maxsize=None)
def act(m, word):
    """L_m applied to L_word |h>, m >= 1, word negative ints (any order)."""
    assert m >= 1
    if not word:
        return {}
    n, rest = word[0], word[1:]
    out = {}
    # L_m L_n rest = L_n (L_m rest) + (m-n) L_{m+n} rest (+ central)
    for w, poly in act(m, rest).items():
        for w2, coef in normal_order((n,) + w).items():
            _dadd(out, w2, pscale(poly, coef))
    k = m + n
    if k < 0:
        for w2, coef in normal_order((k,) + rest).items():
            _dadd(out, w2, pscale(PONE, (m - n) * coef))
    elif k == 0:
        level = -sum(rest)
        _dadd(out, rest, pscale(padd(PH, (Fr(level),)), (m - n)))
        _dadd(out, rest, pscale(PONE, C_CHARGE * (m**3 - m) / 12))
    else:
        for w2, poly in act(k, rest).items():
            _dadd(out, w2, pscale(poly, (m - n)))
    return out

def gram_entry(left, right):
    """<h| L_{y_l}..L_{y_1} L_{-Y'} |h> as poly in h; left/right partitions."""
    comb = {tuple(-p for p in right): PONE}
    for mode in left:  # largest part first = rightmost bra operator acts first
        nxt = {}
        for w, poly in comb.items():
            for w2, poly2 in act(mode, w).items():
                _dadd(nxt, w2, pmul(poly, poly2))
        comb = nxt
    return comb.get((), ())

# ----------------------------------------------------------- vertex (Ward) ops
# matrix element written as z^{-d} * g(z), g = dict zpow -> poly in h.
# d is a global exact rational set before use.

D_EXT = None  # set by set_external_weight

def set_external_weight(dval):
    global D_EXT
    D_EXT = Fr(dval)
    vertex_words.cache_clear()

def ward(m, g):
    """g -> z^m (z g' + m d g), from [L_m,V] acting on z^{-d} g."""
    out = {}
    for k, poly in g.items():
        s = Fr(k) + m * D_EXT
        if s != 0:
            q = pscale(poly, s)
            if q:
                cur = out.get(k + m)
                out[k + m] = padd(cur, q) if cur is not None else q
    return {k: v for k, v in out.items() if v}

@lru_cache(maxsize=None)
def vertex_words(left_word, right_word):
    """<h| L_{left_word reversed order...} V(z) L_{right_word} |h> / z^{-d}.

    left_word: positive modes, the LAST entry acts on V first (adjacent).
    right_word: negative modes word.
    Returns dict zpow -> poly in h."""
    if left_word:
        nearest, short = left_word[-1], left_word[:-1]
        res = ward(nearest, vertex_words(short, right_word))
        out = dict(res)
        for w, poly in act(nearest, right_word).items():
            for k, poly2 in vertex_words(short, w).items():
                q = pmul(poly, poly2)
                if q:
                    cur = out.get(k)
                    out[k] = padd(cur, q) if cur is not None else q
        return {k: v for k, v in out.items() if v}
    if right_word:
        nearest, short = right_word[0], right_word[1:]
        res = ward(nearest, vertex_words((), short))
        return {k: pscale(v, -1) for k, v in res.items()}
    return {0: PONE}

def vertex_entry(left, right):
    """rho entry at z=1 as poly in h."""
    g = vertex_words(tuple(reversed(left)), tuple(-p for p in right))
    tot = ()
    for poly in g.values():
        tot = padd(tot, poly)
    return tot

# ------------------------------------------------------------- level matrices

@lru_cache(maxsize=None)
def basis(level):
    return tuple(partitions(level))

def gram_matrix(level):
    B = basis(level)
    return [[gram_entry(l, r) for r in B] for l in B]

def vertex_matrix(level):
    B = basis(level)
    return [[vertex_entry(l, r) for r in B] for l in B]

# ------------------------------------------------ exact linear algebra helpers

def mat_eval(M, hval):
    return [[peval(e, hval) for e in row] for row in M]

def det_and_trace_inv(G, R):
    """For square Fraction matrices: return (det G, sum_ij (G^{-1})_ij R_ij),
    the latter None if det == 0."""
    n = len(G)
    A = [row[:] + Rrow[:] for row, Rrow in zip(G, R)]  # augmented [G | R]
    det = Fr(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fr(0), None
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = -det
        det *= A[col][col]
        inv = Fr(1) / A[col][col]
        A[col] = [x * inv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    # now left block is identity, right block is G^{-1} R
    # we need sum_ij (G^{-1})_ij R_ij = tr(G^{-1} R^T); careful:
    # right block column j of solution X solves G X = R, X = G^{-1}R,
    # so X_ij = sum_k (G^{-1})_ik R_kj ; trace(X) = sum_ij (G^{-1})_ij R_ji.
    tr = sum(A[i][n + i] for i in range(n))
    return det, tr

# ------------------------------------------------------- rational reconstruction

def lagrange_interp(points):
    """Exact Lagrange interpolation; points list of (x, y) Fractions.
    Returns poly tuple."""
    # Newton's divided differences for stability/efficiency
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    n = len(points)
    coef = ys[:]  # divided differences
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    # build polynomial from Newton form
    poly = ()
    for i in range(n - 1, -1, -1):
        # poly = poly*(x - xs[i]) + coef[i]
        poly = padd(pmul(poly, (-xs[i], Fr(1))), (coef[i],))
    return poly

class RationalFunction:
    """F = num/den, poly tuples."""
    def __init__(self, num, den):
        self.num = num
        self.den = den

    def laurent_at(self, point, kmax):
        """Laurent coefficients a_j, j = -ord .. kmax, at h = point.
        Returns dict j -> Fraction."""
        # shift both num, den to local variable x = h - point
        def shift(p):
            # coefficients of p(point + x): repeated synthetic division
            cur = list(p)
            res = []
            while cur:
                q = [Fr(0)] * (len(cur) - 1)
                acc = cur[-1]
                for i in range(len(cur) - 2, -1, -1):
                    q[i] = acc
                    acc = cur[i] + acc * point
                res.append(acc)  # coefficient of x^k
                cur = list(pnorm(tuple(q)))
            return pnorm(tuple(res))
        ln = shift(self.num)
        ld = shift(self.den)
        vd = 0
        while vd < len(ld) and ld[vd] == 0:
            vd += 1
        vn = 0
        while vn < len(ln) and ln[vn] == 0:
            vn += 1
        if not ln:
            return {}
        ord_pole = vd - vn
        # series of ln/ld = x^{vn-vd} * (ln shifted)/(ld shifted)
        a = ln[vn:]
        bpoly = ld[vd:]
        need = kmax + ord_pole + 1
        inv = []
        b0 = bpoly[0]
        for k in range(need):
            s = a[k] if k < len(a) else Fr(0)
            for j in range(1, min(k, len(bpoly) - 1) + 1):
                s -= bpoly[j] * inv[k - j]
            inv.append(s / b0)
        return {k - ord_pole: inv[k] for k in range(need)}

def reconstruct_F(level, sample_xs=None, verbose=True):
    """Reconstruct F_level(h) = tr(G^{-1} rho^T) exactly as num/den."""
    B = basis(level)
    n = len(B)
    G = gram_matrix(level)
    R = vertex_matrix(level)
    degD = sum(len(Y) for Y in B)
    if verbose:
        print(f"[engine] level {level}: dim {n}, det degree {degD}", flush=True)
    npts = degD + 1
    dets, prods, xs = [], [], []
    x = Fr(3)
    while len(xs) < npts:
        Gx = mat_eval(G, x)
        Rx = mat_eval(R, x)
        det, tr = det_and_trace_inv(Gx, Rx)
        if det != 0:
            xs.append(x)
            dets.append(det)
            prods.append(det * tr)  # = tr * det, a polynomial value
        x += 1
    D = lagrange_interp(list(zip(xs, dets)))
    # numerator degree can equal degD (F bounded at infinity)
    P = lagrange_interp(list(zip(xs, prods)))
    if len(P) > degD + 1:
        raise RuntimeError("numerator degree too high — sampling insufficient")
    # verification at extra point
    xv = xs[-1] + 1
    while True:
        Gx = mat_eval(G, xv)
        Rx = mat_eval(R, xv)
        det, tr = det_and_trace_inv(Gx, Rx)
        if det != 0:
            break
        xv += 1
    assert peval(D, xv) == det and peval(P, xv) == det * tr, "reconstruction failed"
    return RationalFunction(P, D)

EULER = None
def euler_coeffs(nmax):
    e = [Fr(0)] * (nmax + 1)
    e[0] = Fr(1)
    for m in range(1, nmax + 1):
        for k in range(nmax, m - 1, -1):
            e[k] -= e[k - m]
    return e
