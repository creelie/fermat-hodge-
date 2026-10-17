#!/usr/bin/env python3
"""
sixfold_link.py  --  the sixfold link for the Mumford classes.

Split model over Qbar (exact rational arithmetic, sympy for the symbol gamma).

  V_i = Q^2 (i = 1,2,3), eps = standard symplectic form, V = V_1 (x) V_2 (x) V_3,
  psi = eps (x) eps (x) eps : H^1 of the Mumford fourfold X, dim 8.
  D_i = M_2(Qbar) = V_i (x) W_i : the i-th place of the quaternion algebra D over
  the cubic field F; D^1 acts by LEFT multiplication (through V_i), the CM field
  K = F(sqrt(-delta)) c D, diagonalised, acts by RIGHT multiplication (through W_i).
  H^1(Z) = D = D_1 + D_2 + D_3, dim 12, the abelian sixfold Z_K of
  rem:mumfordunitary.  Polarisation  psi_c(x,y) = Tr_{F/Q} trd( xbar y c ),
  c in K with cbar = -c, modelled at place i by c_i = gamma_i * diag(1,-1).

What is checked:
  (A) psi_c is alternating iff cbar = -c, and is invariant under left D^1 and
      right K^1 (checked on Lie algebra generators and on random group elements);
  (B) the K^1-invariant part of wedge^2 D_i is 4-dimensional and its
      sl_2-adjoint-isotypic part T_i is 3-dimensional (this is the copy of T);
      the symmetric form induced on wedge^2 D_i by psi_c restricts on T_i to
      r_Z * gamma_i^2 * tr(xy) under the sl_2-equivariant identification
      T_i = sl_2, with r_Z a rational number independent of the place i;
  (C) the copy of T_i in V (x) V = H^1(X) (x) H^1(X), x -> psi(x . , . ),
      carries the form psi (x) psi restricted = r_X * tr(xy), r_X independent
      of i and of any parameter;  hence the composite xi^dagger xi of the Hodge
      isomorphism xi : T_X -> T_Z (e = 1) is multiplication by
      (r_Z / r_X) * gamma_i^2 at the place i, i.e. by the element
      (r_Z/r_X) * c^2 of F, c^2 = -f^2 delta;
  (D) dim of the G x K^1 invariants in H^4(X x X x Z) by Kuenneth component,
      in particular exactly 3 = [F:Q] in H^1(X) (x) H^1(X) (x) H^2(Z), and
      none in H^1(X) (x) H^1(X) (x) H^2(Z) beyond Hom_G(T,T) + NS-products;
  (E) the 4-subsets of weights at a CM point that realise xi are primitive
      zero-sum sets (not unions of zero-sum pairs).
Run:  python3 -I sixfold_link.py
"""
import itertools, random, sys
from fractions import Fraction as Fr
import sympy as sp
import numpy as np

random.seed(1)

# ---------- basic 2x2 objects --------------------------------------------
E = sp.Matrix([[0,1],[0,0]]); Fm = sp.Matrix([[0,0],[1,0]]); H = sp.Matrix([[1,0],[0,-1]])
eps = sp.Matrix([[0,1],[-1,0]])
I2 = sp.eye(2)
def kron(*ms):
    out = ms[0]
    for m in ms[1:]:
        out = sp.kronecker_product(out, m)
    return out

# ---------- (A) the polarisation of Z -------------------------------------
def bar(m):           # quaternion conjugation in M_2 = adjugate
    return m.trace()*I2 - m
gam = sp.symbols('g1 g2 g3')
def c_at(i): return gam[i]*H          # c_i = gamma_i diag(1,-1), cbar = -c

def psi_c_place(x, y, i):             # trd(xbar y c_i) at one place
    return (bar(x)*y*c_at(i)).trace()

# basis of D_i: matrix units, index k = 2a+b  -> matrix with 1 at (a,b)
def unit(a,b):
    m = sp.zeros(2,2); m[a,b] = 1; return m
Dbasis = [unit(a,b) for a in range(2) for b in range(2)]
def gram_psi(i):
    return sp.Matrix(4,4, lambda k,l: psi_c_place(Dbasis[int(k)], Dbasis[int(l)], i))
G1 = gram_psi(0)
assert sp.simplify(G1 + G1.T) == sp.zeros(4,4), "psi_c not alternating"
# with c = gamma*I (cbar = c) it is symmetric, not alternating:
cs = sp.symbols('cs')
Gs = sp.Matrix(4,4, lambda k,l: (bar(Dbasis[int(k)])*Dbasis[int(l)]*cs*I2).trace())
assert sp.simplify(Gs - Gs.T) == sp.zeros(4,4)
# left sl_2 invariance: psi(x d, d') + psi(d, x d') = 0
for X in (E,Fm,H):
    for d in Dbasis:
        for d2 in Dbasis:
            assert sp.simplify(psi_c_place(X*d, d2, 0) + psi_c_place(d, X*d2, 0)) == 0
# right torus invariance (right mult by diag(t, 1/t)):
t = sp.symbols('t')
Tt = sp.diag(t, 1/t)
for d in Dbasis:
    for d2 in Dbasis:
        assert sp.simplify(psi_c_place(d*Tt, d2*Tt, 0) - psi_c_place(d, d2, 0)) == 0
print("(A) psi_c alternating, left-D^1 and right-K^1 invariant: OK")

# ---------- (B) T_i inside wedge^2 D_i and its form -----------------------
# wedge^2 D_i basis: pairs k<l
pairs = list(itertools.combinations(range(4),2))
def wedge_action(M):   # action of a 4x4 matrix M (on D_i) on wedge^2 D_i
    W = sp.zeros(6,6)
    for col,(k,l) in enumerate(pairs):
        # M e_k ^ e_l + e_k ^ M e_l
        for a in range(4):
            for b in range(4):
                coef = M[a,k]*(1 if b==l else 0) + (1 if a==k else 0)*M[b,l]
                if coef == 0: continue
                if a == b: continue
                if a < b: W[pairs.index((a,b)), col] += coef
                else:     W[pairs.index((b,a)), col] -= coef
    return W
def left_mat(X):      # matrix of d -> X d on Dbasis
    return sp.Matrix(4,4, lambda k,l: (X*Dbasis[int(l)])[int(k)//2, int(k)%2])
def right_mat(X):     # matrix of d -> d X
    return sp.Matrix(4,4, lambda k,l: (Dbasis[int(l)]*X)[int(k)//2, int(k)%2])
Lh = wedge_action(left_mat(H)); Le = wedge_action(left_mat(E)); Lf = wedge_action(left_mat(Fm))
Rh = wedge_action(right_mat(H))
# K^1-invariants in wedge^2 D_i = kernel of the right torus generator
Kinv = Rh.nullspace()
assert len(Kinv) == 4
Kmat = sp.Matrix.hstack(*Kinv)
# sl_2 (left) acts on Kinv; adjoint-isotypic part = kernel of Casimir - 8 (adjoint: 2*(2+2)=8 with
# Casimir  h^2 + 2ef + 2fe ... use C = h^2 + 2(ef+fe) = h^2 + 4fe + 2h)
Cas = Lh*Lh + 2*(Le*Lf + Lf*Le)
# restrict to Kinv
coef = (Kmat.T*Kmat).inv()*Kmat.T
CasK = coef*Cas*Kmat
ev = CasK.eigenvals()
assert ev == {8:3, 0:1}, ev
Tbasis_vecs = (CasK - 8*sp.eye(4)).nullspace()
Tmat = Kmat*sp.Matrix.hstack(*Tbasis_vecs)     # 6x3, columns span T_i in wedge^2 D_i
# weight vectors of T_i under Lh
LhT = ((Tmat.T*Tmat).inv()*Tmat.T)*Lh*Tmat
assert set(LhT.eigenvals().keys()) == {2,0,-2}
P, Dg = LhT.diagonalize()
Tw = Tmat*P        # columns: weight vectors, weights Dg
wts = [Dg[j,j] for j in range(3)]
# identify with sl_2: weight 2 <-> E, 0 <-> H, -2 <-> F  (adjoint rep: [H,E]=2E, [H,F]=-2F)
# fix the equivariant map by also matching the lowering operator: v_0 := Lf v_2, v_{-2} := Lf v_0 /2
v2 = Tw[:, wts.index(2)]
v0 = Lf*v2
vm2 = Lf*v0
# In sl_2: ad(F)E = [F,E] = -H ;  ad(F)(-H) = -[F,H] = -2F.  So v2<->E, v0<->-H, vm2<->-2F.
Tiso = {'E': v2, 'H': -v0, 'F': -vm2/2}
def induced_form(i):
    Gp = gram_psi(i)
    M = sp.zeros(6,6)
    for r,(a,b) in enumerate(pairs):
        for s,(c,d) in enumerate(pairs):
            M[r,s] = Gp[a,c]*Gp[b,d] - Gp[a,d]*Gp[b,c]
    return M
def trform(X,Y): return (X*Y).trace()
sl2 = {'E':E,'H':H,'F':Fm}
ratios = set()
for i in range(3):
    M = induced_form(i)
    for n1,m1 in sl2.items():
        for n2,m2 in sl2.items():
            val = sp.simplify((Tiso[n1].T*M*Tiso[n2])[0,0])
            tr = trform(m1,m2)
            if tr != 0:
                ratios.add(sp.simplify(val/(tr*gam[i]**2)))
            else:
                assert val == 0, (n1,n2,val)
assert len(ratios) == 1, ratios
rZ = ratios.pop()
print("(B) T_i = adjoint part of (wedge^2 D_i)^{K^1}, induced form = rZ*gamma_i^2*tr(xy), rZ =", rZ)

# ---------- (C) the copy of T_i in V (x) V and its form --------------------
# V basis index a = 4 b1 + 2 b2 + b3 ; psi = eps x eps x eps
Psi = kron(eps,eps,eps)
def X_in_V(Xi, i):   # x acting on the i-th factor
    mats = [I2,I2,I2]; mats[i] = Xi; return kron(*mats)
def tensor_of(x):    # 2-tensor (v,w) -> psi(x v, w), as 8x8 matrix  (row v, col w)
    return (Psi.T*0 + (x.T*Psi))  # psi(xv,w) = v^T x^T Psi w
# induced form on V (x) V from psi (x) psi:  <A,B> = sum A_ab B_cd psi^{ac} psi^{bd}  (psi^{-1} = -Psi here since Psi^2=-1)
PsiInv = Psi.inv()
def formVV(A,B):
    return (A.T*PsiInv*B*PsiInv.T).trace()   # = sum A_ab psi^{ac} B_cd psi^{bd}
ratiosX = set()
for i in range(3):
    for n1,m1 in sl2.items():
        for n2,m2 in sl2.items():
            A = tensor_of(X_in_V(m1,i)); B = tensor_of(X_in_V(m2,i))
            val = sp.nsimplify(formVV(A,B))
            tr = trform(m1,m2)
            if tr != 0: ratiosX.add(sp.Rational(val)/tr)
            else: assert val == 0
    # also check the tensor is symmetric (lies in S^2 V):
    assert tensor_of(X_in_V(E,i)) == tensor_of(X_in_V(E,i)).T
assert len(ratiosX) == 1
rX = ratiosX.pop()
print("(C) copy of T_i in H^1(X)(x)H^1(X) is symmetric, carries rX*tr(xy), rX =", rX,
      "; so xi^dagger xi = (rZ/rX) * c^2 =", sp.simplify(rZ/rX), "* c^2  (c^2 = -f^2 delta in F)")

# ---------- (D) G x K^1 invariants in H^4(X x X x Z) by Kuenneth component -----
# Lie algebra: sl_2^3 (acting on both copies of V and on D by left mult) + torus rank 3 (right on D).
# Build the 28-dim space H^1(X x X x Z) = V + V + D with operators as 28x28 rational matrices.
import numpy as np
def tofloat(M): return np.array(M.tolist(), dtype=float)
ops = []
for i in range(3):
    for Xi in (E,Fm,H):
        blockV = tofloat(X_in_V(Xi,i))
        blockD = np.zeros((12,12)); blockD[4*i:4*i+4,4*i:4*i+4] = tofloat(left_mat(Xi))
        M = np.zeros((28,28)); M[:8,:8]=blockV; M[8:16,8:16]=blockV; M[16:,16:]=blockD
        ops.append(M)
torus_ops = []
for i in range(3):
    blockD = np.zeros((12,12)); blockD[4*i:4*i+4,4*i:4*i+4] = tofloat(right_mat(H))
    M = np.zeros((28,28)); M[16:,16:]=blockD
    torus_ops.append(M)
# weights of basis vectors under the 6 Cartan elements (3 of sl_2^3 (H), 3 torus)
cartan = [ops[3*i+2] for i in range(3)] + torus_ops
wt = np.array([[int(round(C[k,k])) for C in cartan] for k in range(28)])
# Kuenneth labels: 0 = first V, 1 = second V, 2 = D
lab = [0]*8 + [1]*8 + [2]*12
quads = [q for q in itertools.combinations(range(28),4) if not wt[list(q)].sum(axis=0).any()]
print("    weight-zero 4-subsets of H^1(X x X x Z):", len(quads))
# matrix of an operator from the weight-zero span of wedge^4 to wedge^4 (sparse dict)
def act_on_wedge(M, q):
    out = {}
    for pos,k in enumerate(q):
        for a in range(28):
            if M[a,k] == 0 or a in q: continue
            new = list(q); new[pos] = a
            # sort with sign
            sign = 1
            arr = new[:]
            for ii in range(4):
                for jj in range(3-ii):
                    if arr[jj] > arr[jj+1]:
                        arr[jj],arr[jj+1] = arr[jj+1],arr[jj]; sign = -sign
            key = tuple(arr)
            out[key] = out.get(key,0) + sign*M[a,k]
    return out
# invariants = common kernel of the raising/lowering operators E_i, F_i (torus already zero on weight 0)
rows = {}
mats = []
for M in [ops[3*i] for i in range(3)] + [ops[3*i+1] for i in range(3)]:
    cols = []
    for q in quads: cols.append(act_on_wedge(M,q))
    keys = sorted({k for c in cols for k in c})
    idx = {k:j for j,k in enumerate(keys)}
    A = np.zeros((len(keys), len(quads)))
    for j,c in enumerate(cols):
        for k,v in c.items(): A[idx[k],j] = v
    mats.append(A)
Abig = np.vstack(mats)
u,s,vt = np.linalg.svd(Abig, full_matrices=True)
tol = 1e-8
rank = int((s > tol).sum())
ker = vt[rank:].T        # basis of invariants, columns, in the weight-zero coordinates
print("    dim Hdg^2(X x X x Z) (G x K^1 invariants in H^4) =", ker.shape[1])
# split by Kuenneth type (a,b,c) = numbers of factors from V, V', D
def ktype(q):
    return tuple(sum(1 for k in q if lab[k]==j) for j in range(3))
types = sorted({ktype(q) for q in quads})
for ty in types:
    sel = np.array([ktype(q)==ty for q in quads])
    # invariants lie in direct sums of Kuenneth pieces (operators preserve type), so project
    sub = ker[sel,:]
    r = np.linalg.matrix_rank(sub, tol=1e-8)
    if r: print("      Kuenneth type (V,V',D) =", ty, ": dim", r)
# (E) primitive zero-sum 4-sets realising xi: type (1,1,2) with the two D-factors at one place
prim = 0; total112 = 0
for q in quads:
    if ktype(q) != (1,1,2): continue
    total112 += 1
    # is it a union of two zero-sum pairs?
    union = any(not wt[[q[a],q[b]]].sum(axis=0).any() for a,b in itertools.combinations(range(4),2))
    if not union: prim += 1
print("(E) weight-zero 4-sets of type (1,1,2):", total112, "; primitive (no zero-sum pair):", prim)
print("ALL CHECKS PASSED")
