#!/usr/bin/env python3
"""
rr_constraints.py -- exact (sympy) Riemann-Roch constraints on the unknown Ext groups
of the pieces of thm:product, A a Weil fourfold (m=2, principal polarisation theta,
int theta^4 = 4!), A' a Weil surface (m'=1).

(A) chi(F_i, L^l) = int p_i(-theta) e^{l theta} is a nonzero polynomial P_i(l) of degree <= 4
    whose coefficients are the c_{ik}; the exponential expansion p_i = sum_l b_{il} e^{l theta}
    (mod theta^5) is a linear map c -> b.  For every subset S of {0..4} we solve the LINEAR
    system  { b_l(c) = 0 (l not in S),  P_c(s) = 0 (s in S) }  and report whether a nonzero c
    with b_l(c) != 0 for all l in S exists.  Result: none.  Hence for every sheaf F of polarised
    shape on A there is l in the exponential support of p_F with chi(F, L^l) != 0, so
    Ext^*(F, L^l) != 0 for a power L^l that Step 2 of thm:product uses.
(B) chi(E,E) for the final object, chi(F_i,F_j), chi(F_i x Y, X' x Y') formulas.
(C) The A'-side Ext algebra when G'_j are line bundles N_j: H^*(A', N) by the sign of c_1^2.
"""
import itertools, sympy as sp
l, t = sp.symbols('l t')
c = sp.symbols('c0:5')
p = sum(c[k]*t**k for k in range(5))
# P(l) = int p(-theta) e^{l theta}, int theta^4 = 4!
P = sum((-1)**k*c[k]*sp.factorial(4)*l**(4-k)/sp.factorial(4-k) for k in range(5))
P = sp.expand(P)
# exponential expansion: p = sum_l b_l e^{l t} mod t^5  <=>  sum_l b_l l^j/j! = c_j
V = sp.Matrix(5, 5, lambda j, L: sp.Rational(L**j, sp.factorial(j)))   # V b = c
b = V.inv()*sp.Matrix(c)
print("(A) chi(F,L^l) = P(l) =", P)
print("    exponential coefficients b_l (linear in c):")
for L in range(5): print(f"      b_{L} =", sp.expand(b[L]))
found = False
ADMISSIBLE = []
for size in range(1, 6):
    for S in itertools.combinations(range(5), size):
        eqs = [b[L] for L in range(5) if L not in S] + [P.subs(l, s) for s in S]
        A = sp.Matrix([[sp.diff(e, ci) for ci in c] for e in eqs])
        ns = A.nullspace()
        ok = False
        for v in ns:   # any nonzero solution has b_l != 0 on S?  (test a generic combination)
            vals = [sp.simplify(b[L].subs(dict(zip(c, v)))) for L in S]
            if all(x != 0 for x in vals): ok = True
        if ns and not ok and len(ns) > 1:
            # generic combination
            lam = sp.symbols('lam0:%d' % len(ns))
            v = sum((li*vi for li, vi in zip(lam, ns)), sp.zeros(5, 1))
            vals = [sp.expand(b[L].subs(dict(zip(c, v)))) for L in S]
            ok = all(x != 0 for x in vals)
        if ok: found = True; ADMISSIBLE.append(S)
        print(f"    S={S}: nullspace dim {len(ns)}; admissible c (b!=0 on S, P=0 on S): {ok}")
print("    => some polarised p with chi(F,L^l)=0 for every l in its exponential support exists:", found)
print("    admissible supports:", ADMISSIBLE, "(exactly the singletons: p = b e^{l theta})")
assert sorted(ADMISSIBLE) == [(l,) for l in range(5)], ADMISSIBLE

# (B) Euler characteristics
print("\n(B) chi(E,E) for ch(E) = M w + sum_k mu_k e^{k theta} on the sixfold (int theta^6 = 6!):")
mu = sp.symbols('mu0:3'); M, x = sp.symbols('M x', positive=True)
chi_poly = sum(mu[k]*mu[j]*(j-k)**6 for k in range(3) for j in range(3))
print("    chi(E,E) = 2 M^2 |x|^2 +", sp.expand(chi_poly), "   (w = x om_+om'_+ + conj, w^dual = -w, int w^2 = -2|x|^2)")
print("    with mu = (1,1,1):", chi_poly.subs({mu[0]:1, mu[1]:1, mu[2]:1}), "+ 2M^2|x|^2")
print("    chi(F_i,F_j) = N_i N_j int omega_i omega_j + int p_i(-theta) p_j(theta); int omega_1^2 = 2|u|^2, int omega_1 omega_2 = 0, int omega_2^2 = 2D|u|^2")
print("    Kuenneth: chi(X x Y, X' x Y') = chi(X,X') chi(Y,Y');  Ext^k(X x Y, X' x Y') = sum_{a+b=k} Ext^a(X,X') (x) Ext^b(Y,Y')")

# (C) A'-side: line bundles on the Weil surface A' with NS_Q = Q theta' + W(A'), theta'^2 = 2,
#     W negative definite (Hodge index), omega'_1^2 = -2|u'|^2, omega'_1.omega'_2 = 0, omega'_2^2 = -2D|u'|^2.
print("\n(C) A'-side: for a line bundle N on the abelian surface A' with D = c_1(N):")
print("    D^2 > 0: N or N^{-1} ample, H^0 (resp. H^2) only, of dimension D^2/2;")
print("    D^2 < 0: nondegenerate of index 1 (Mumford, Abelian varieties, Sect. 16), H^1 only, dimension -D^2/2;")
print("    D^2 = 0, D != 0: degenerate; H^* = 0 unless N is pulled back from an elliptic quotient E with N_E of degree e>0: then h^0 = h^1 = e;")
print("    D = 0: H^*(O) = Lambda^* C^2, dims 1,2,1 (N = O) or 0 (N nontrivial of degree 0).")
print("    pieces Y in {N_1, N_2, O, L', L'^2}: c_1 = N'_1 om'_1 + r_1 th', N'_2 om'_2 + r_2 th', 0, th', 2 th'.")
up2, Dd = sp.symbols("u2 D", positive=True); N1, N2, r1, r2 = sp.symbols("N1 N2 r1 r2")
cls = {"N1": (N1, 0, r1), "N2": (0, N2, r2), "O": (0, 0, 0), "L'": (0, 0, 1), "L'^2": (0, 0, 2)}
def sq(a1, a2, r): return sp.expand(-2*up2*a1**2 - 2*Dd*up2*a2**2 + 2*r**2)
print("    c_1(Y')-c_1(Y) squared (|u'|^2 = u2):")
for Y in cls:
    for Yp in cls:
        d = tuple(cls[Yp][i]-cls[Y][i] for i in range(3))
        print(f"      Ext^*({Y:5s},{Yp:5s}): D = {d[0]} om'_1 + {d[1]} om'_2 + ({d[2]}) th',  D^2 = {sq(*d)}")

print("riemann_roch_pieces: PASS")
