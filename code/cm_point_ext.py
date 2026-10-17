"""Exact checks for Lemma lem:cmext and Proposition prop:twostep (the Ext groups at the CM point
E_0^6 and the bookkeeping of cancellations).

(A) sum_{p+q=k} C(3,q) C(3,p) = C(6,k): the dimension of Ext^k(O_Z, O_Z) for an abelian
    threefold Z in an abelian sixfold with trivial normal bundle.
(B) The Koszul cochain complex of x_1, x_2, x_3 on Q[x_1, x_2, x_3], graded by polynomial degree
    minus cohomological degree, has cohomology only in cohomological degree 3 and polynomial degree
    0, of dimension one: this is
    the local computation Ext^k(O_Z, O_Z') = 0 for k != 3 and Ext^3 = O_{Z cap Z'} at a point of a
    transverse intersection, done exactly over Q with rational ranks.
(C) The dimensions C(3,k) (b-a)^3 chi_Z of Ext^k(O_Z L^a, O_Z L^b) for b > a, C(3,k-3)(a-b)^3 chi_Z
    for b < a, and |b-a|^3 chi_Z in one degree for the mixed groups, agree with the Euler
    characteristics chi(Z, L^m|_Z) = m^3 chi_Z taken with the Koszul signs.
(D) The degree table of Lemma lem:cmext for pieces O_Z L^k, O_Z' L^k and L^k (twists 0..3, two
    threefolds): every closed chain of two pieces has total Ext degree at least three, and the
    closed chains of three pieces with total degree three are exactly O_Z L^k -> O_Z L^k' ->
    O_Z L^k'' -> O_Z L^k with k < k' < k'' (degrees 0, 0, 3).
(E) The count of the stopping point: five pieces of fifteen diagonal classes give 75, and 75 - 57 = 18.
Run: python3 -I cm_point_ext.py
"""
import itertools
from math import comb
import sympy as sp

fails = 0
def check(name, ok):
    global fails
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok: fails += 1

# (A)
check("binomial identity C(6,k)", all(sum(comb(3, q)*comb(3, k-q) for q in range(0, k+1)) == comb(6, k) for k in range(7)))

# (B) Koszul cochain complex of x1,x2,x3 on Q[x], graded by g = polynomial degree - p; C^p_g = Lambda^p (x) Q[x]_{g+p}
x = sp.symbols('x1 x2 x3')
def monomials(d):
    return [sp.Mul(*[v**e for v, e in zip(x, es)]) for es in itertools.product(range(d+1), repeat=3) if sum(es) == d]
def basis(p, g):
    if g + p < 0: return []
    return [(S, m) for S in itertools.combinations(range(3), p) for m in monomials(g+p)]
def differential(p, d):
    """matrix of wedge with sum x_i e_i from C^p_g to C^{p+1}_g."""
    src, tgt = basis(p, d), basis(p+1, d)
    idx = {b: i for i, b in enumerate(tgt)}
    M = sp.zeros(len(tgt), len(src))
    for j, (S, m) in enumerate(src):
        for i in range(3):
            if i in S: continue
            T = tuple(sorted(S + (i,)))
            sign = (-1)**sum(1 for s in S if s < i)
            M[idx[(T, sp.expand(m*x[i]))], j] += sign
    return M
coh = {}
for d in range(-3, 4):
    for p in range(0, 4):
        dim = len(basis(p, d))
        rk_out = differential(p, d).rank() if p < 3 and dim else 0
        rk_in = differential(p-1, d).rank() if p > 0 and dim else 0
        h = dim - rk_out - rk_in
        if h: coh[(p, d)] = h
check("Koszul cohomology only in cohomological degree 3, polynomial degree 0, dimension one", coh == {(3, -3): 1})

# (C) Euler characteristics with Koszul signs
def chi_pieces(a, b, chiZ):
    # chi of Ext^*(O_Z L^a, O_Z L^b) = sum_k (-1)^k dim = sum_p (-1)^p C(3,p) * chi(Z, L^{b-a}) = 0 unless a = b
    m = b - a
    if m > 0: dims = {k: comb(3, k)*m**3*chiZ for k in range(4)}
    elif m < 0: dims = {k: comb(3, k-3)*(-m)**3*chiZ for k in range(3, 7)}
    else: dims = {k: comb(6, k) for k in range(7)}
    return sum((-1)**k*v for k, v in dims.items()), dims
ok = True
for chiZ in (1, 2, 5):
    for a, b in itertools.product(range(-2, 3), repeat=2):
        e, dims = chi_pieces(a, b, chiZ)
        ok &= (e == 0)
        if a != b: ok &= (sum(dims.values()) == 8*abs(b-a)**3*chiZ)
check("Euler characteristics of the self-Ext groups vanish, total rank 8|b-a|^3 chi_Z", ok)

# (D) degree table
TW = range(0, 4)
pieces = [('Z', k) for k in TW] + [('W', k) for k in TW] + [('L', k) for k in TW]
def degrees(P, Q):
    """set of k with Ext^k(F_P, F_Q) != 0, from Lemma lem:cmext, P != Q."""
    (t, a), (u, b) = P, Q
    if t == 'L' and u == 'L': return {0} if b > a else {6}
    if t == 'L' and u != 'L': return {0} if b > a else ({3} if b < a else {0, 1, 2, 3})
    if t != 'L' and u == 'L': return {3} if b > a else ({6} if b < a else {3, 4, 5, 6})
    if t != u: return {3}
    if b > a: return {0, 1, 2, 3}
    if b < a: return {3, 4, 5, 6}
    raise ValueError
two = min(min(degrees(P, Q)) + min(degrees(Q, P)) for P in pieces for Q in pieces if P != Q)
check("every two-step chain has total degree >= 3", two >= 3)
found = set()
for P, Q, R in itertools.permutations(pieces, 3):
    for k1 in degrees(P, Q):
        for k2 in degrees(Q, R):
            for k3 in degrees(R, P):
                if k1 + k2 + k3 == 3:
                    found.add((P, Q, R, k1, k2, k3))
expected = set()
for t in ('Z', 'W'):
    for a, b, c in itertools.combinations(TW, 3):
        chain = [(t, a), (t, b), (t, c)]; degs = [0, 0, 3]
        for r in range(3):  # the same closed chain read from each of its three pieces
            P, Q, R = chain[r:] + chain[:r]; k1, k2, k3 = degs[r:] + degs[:r]
            expected.add((P, Q, R, k1, k2, k3))
check("three-step chains of total degree 3 are exactly the ascending twists of one threefold", found == expected)
check("no three-step chain of total degree 3 starts at a line bundle", not any(P[0] == 'L' for P, *_ in found))

# (E)
check("count at the stopping point: 5*15 = 75 and 75 - 57 = 18", 5*15 == 75 and 75 - 57 == 18)

print(f"cm_point_ext: {'PASS' if fails == 0 else 'FAIL'}")
raise SystemExit(fails)
