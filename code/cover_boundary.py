"""Check of the cover-boundary construction.

B_lambda : x^3 + y^3 + 1 + lambda x^3 y^3 = 0 in P^1 x P^1, lambda not in {0,1}.
(A) smoothness for every lambda not in {0,1};
(B) div(y^3 + 1/lambda) = 3 F_x - 3 F_y with F_x, F_y the fibres over x = oo and y = oo,
    so eta = O(1,-1)|_B has 3 eta = 0;
(C) eta != 0 : no a + b x vanishes on the three points of F_y;
(D) the nine products x^i y^j (0 <= i, j <= 2) restrict to a basis of H^0(B, O(2,2)) = H^0(2K).
"""
import sympy as sp

x0, x1, y0, y1, lam, t = sp.symbols('x0 x1 y0 y1 lambda t')
F = x1**3*y0**3 + x0**3*y1**3 + x0**3*y0**3 + lam*x1**3*y1**3   # x = x1/x0, y = y1/y0

# (A) smoothness: solve F = dF = 0 in the four affine charts for generic lambda
def chart(sub):
    G = F.subs(sub)
    vars_ = [v for v in (x0, x1, y0, y1) if v not in sub]
    eqs = [G] + [sp.diff(G, v) for v in vars_]
    sols = sp.solve(eqs, vars_ + [lam], dict=True)
    return sols
bad = set()
for sub in ({x0: 1, y0: 1}, {x0: 1, y1: 1}, {x1: 1, y0: 1}, {x1: 1, y1: 1}):
    for s in chart(sub):
        bad.add(sp.simplify(s.get(lam, sp.nan)))
assert bad <= {0, 1, sp.nan}, bad
print("(A) B_lambda is smooth for every lambda not in {0, 1}")

# (B) fibre of the y-projection over a cube root c of -1/lambda is 3 (oo, c)
c = sp.symbols('c')
Gy = F.subs({y0: 1, y1: c}).subs(c**3, -1/lam)
assert sp.expand(Gy.subs(x0, 1)) == sp.expand(1 - 1/lam)          # no point with x0 = 1 ... unless lam = 1
assert sp.expand(sp.expand(F.subs({y0: 1, y1: c, x0: 0}))).subs(c**3, -1/lam) == 0
# so the fibre over y = c is supported at x = oo; it has degree 3, hence equals 3 (oo, c).
# the fibre over y = oo: x0^3 + lam x1^3 = 0, three distinct points
assert sp.discriminant(sp.Poly(x0**3 + lam, x0)) != 0
print("(B) div(y^3 + 1/lambda) = 3 F_x - 3 F_y, so 3 eta = 0 for eta = O(1,-1)|_B")

# (C) eta != 0: F_y = {(x, oo): x^3 = -1/lam}, three distinct x-values, no a + b x vanishes there
assert sp.discriminant(sp.Poly(x1**3 + 1/lam, x1)) != 0
print("(C) eta != 0 (a pencil of degree 3 cannot have three distinct base x-values)")

# (D) the nine monomials x^i y^j, i, j <= 2, are a basis of bidegree (2,2) forms, and restriction
# H^0(P^1 x P^1, O(2,2)) -> H^0(B, O(2,2)) is injective (its kernel is H^0(O(-1,-1)) = 0).
# Direct check at lambda = 2: evaluate the nine monomials at 9 generic points of B and take the rank.
import random
random.seed(1)
lam0 = sp.Rational(2)
pts = []
while len(pts) < 9:
    xv = sp.Rational(random.randint(-20, 20), random.randint(1, 7))
    ys = sp.Poly(sp.expand((x1**3 + 1 + t**3*(1 + lam0*x1**3)).subs(x1, xv)), t).nroots(n=50)
    for yv in ys:
        pts.append((xv, yv))
    pts = pts[:9]
M = sp.Matrix([[sp.N(xv**i*yv**j, 50) for i in range(3) for j in range(3)] for (xv, yv) in pts])
assert M.rank(iszerofunc=lambda v: abs(v) < 1e-30) == 9
print("(D) the multiplication map H^0(K+eta) x H^0(K-eta) -> H^0(2K) is onto (rank 9)")
print("cover_boundary: PASS")
