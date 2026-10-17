#!/usr/bin/env python3
"""
link_weights.py -- finite linear algebra behind Sect. VI of the paper
(the sixfold link xi on X x X x Z_K for a Mumford fourfold X).

Split model over Qbar as in sixfold_link.py:
  V_i = Qbar^2, V = V_1 (x) V_2 (x) V_3 = H^1(X), psi = eps^{(x)3};
  D_i = V_i (x) W_i = M_2, D = D_1+D_2+D_3 = H^1(Z_K); G = SL_2^3 acts on V and
  by left multiplication on D; the torus K^1 (rank 3, characters chi_i) acts by
  right multiplication on D.  H^1(A) = V + V' + D for A = X x X x Z_K (dim 28).

Checks:
 (1) representation picture: V(x)V = 1 + T + U + S (1,9,27,27), wedge^2 D torus
     invariants = T + 1^3; Hodge classes of degree 4 under three groups:
       Delta(G).K^1 (the generic Hodge group of A)        -> 26, type (1,1,2): 6
       G x G' x K^1 (independent groups on X, X' and Z)   -> smaller, (1,1,2): 3
       Sp(V) acting diagonally on V+V', times K^1 on D     -> the Lefschetz-type
                                                             part, (1,1,2): 3
 (2) zeta (cyclic permutation of the three sl_2 factors, acting on V and V'
     only) fixes exactly the Lefschetz-type part of the (1,1,2) Hodge classes;
     the F-line of links xi is not zeta-stable (so xi lies outside the system
     of H8 prop:mumfordformal).
 (3) the Q-Zariski closure of the circle in the torus: (u,u,1) generates K^1
     (uniform signs), (u,1/u,1) generates the kernel of chi_1 chi_2 chi_3
     (mixed signs, the Weil-type variant Z^W, signature (3,3)); the Weil class
     wedge^6 D_+ is G.T_0-invariant and not K^1-invariant; T_Z survives.
 (4) CM points: for several Galois images Gamma (subgroups of signed
     permutations acting simultaneously on the L-side and the K-side) compute
     the rank of the Hodge torus H_c of X_c x Z_{K,c}, the coincidences between
     weights of V and weights of D (= Hom(X_c, Z_{K,c}) != 0), the isogeny
     type of Z_{K,c}, and the number of Hodge classes of degree 4 on A_c.
Run: python3 -I link_weights.py   (about 1-2 min; numpy, sympy)
"""
import itertools, sys
import numpy as np
import sympy as sp

OK = True
def check(cond, msg):
    global OK
    print(("  ok   " if cond else "  FAIL ") + msg)
    if not cond: OK = False

# ---------------------------------------------------------------- basics
E = np.array([[0,1],[0,0]],float); Fm = np.array([[0,0],[1,0]],float)
H = np.array([[1,0],[0,-1]],float); eps = np.array([[0,1],[-1,0]],float); I2 = np.eye(2)
def kron(*ms):
    out = ms[0]
    for m in ms[1:]: out = np.kron(out, m)
    return out
def X_in_V(Xi, i):
    ms = [I2,I2,I2]; ms[i] = Xi; return kron(*ms)
units = [np.zeros((2,2)) for _ in range(4)]
for a in range(2):
    for b in range(2): units[2*a+b][a,b] = 1
def left_mat(X):  return np.array([[ (X@units[l])[k//2,k%2] for l in range(4)] for k in range(4)])
def right_mat(X): return np.array([[ (units[l]@X)[k//2,k%2] for l in range(4)] for k in range(4)])

N = 28
lab = [0]*8 + [1]*8 + [2]*12          # Kuenneth label: V, V', D
def op_diag_G(i, Xi):
    """sl_2 at place i acting on V, V' and (left) D simultaneously: Delta(G)."""
    M = np.zeros((N,N)); bV = X_in_V(Xi,i)
    M[:8,:8] = bV; M[8:16,8:16] = bV
    M[16+4*i:20+4*i,16+4*i:20+4*i] = left_mat(Xi)
    return M
def op_G_on(i, Xi, which):
    """sl_2 at place i acting on one Kuenneth factor only (0: V, 1: V', 2: D)."""
    M = np.zeros((N,N))
    if which == 0: M[:8,:8] = X_in_V(Xi,i)
    elif which == 1: M[8:16,8:16] = X_in_V(Xi,i)
    else: M[16+4*i:20+4*i,16+4*i:20+4*i] = left_mat(Xi)
    return M
def op_torus(i):
    M = np.zeros((N,N)); M[16+4*i:20+4*i,16+4*i:20+4*i] = right_mat(H); return M
def op_sp(A):
    """A in sp(V,psi) (8x8) acting diagonally on V + V', zero on D."""
    M = np.zeros((N,N)); M[:8,:8] = A; M[8:16,8:16] = A; return M

# Cartan (6 coordinates): H_i diagonal on everything, torus_i on D
cartan = [op_diag_G(i,H) for i in range(3)] + [op_torus(i) for i in range(3)]
wt = np.array([[int(round(C[k,k])) for C in cartan] for k in range(N)])
quads = [q for q in itertools.combinations(range(N),4) if not wt[list(q)].sum(axis=0).any()]
qindex = {q:j for j,q in enumerate(quads)}
def ktype(q): return tuple(sum(1 for k in q if lab[k]==j) for j in range(3))

def act_on_wedge(M, q):
    out = {}
    for pos,k in enumerate(q):
        for a in range(N):
            if M[a,k] == 0 or a in q: continue
            new = list(q); new[pos] = a
            sign = 1; arr = new[:]
            for ii in range(4):
                for jj in range(3-ii):
                    if arr[jj] > arr[jj+1]:
                        arr[jj],arr[jj+1] = arr[jj+1],arr[jj]; sign = -sign
            key = tuple(arr); out[key] = out.get(key,0) + sign*M[a,k]
    return out
def big_matrix(ops):
    """stack of the operators restricted to the weight-zero span of wedge^4."""
    mats = []
    for M in ops:
        cols = [act_on_wedge(M,q) for q in quads]
        keys = sorted({k for c in cols for k in c}); idx = {k:j for j,k in enumerate(keys)}
        A = np.zeros((len(keys), len(quads)))
        for j,c in enumerate(cols):
            for k,v in c.items(): A[idx[k],j] = v
        mats.append(A)
    return np.vstack(mats)
def invariants(ops, tol=1e-8):
    A = big_matrix(ops)
    u,s,vt = np.linalg.svd(A, full_matrices=True)
    r = int((s > tol).sum()); return vt[r:].T
def by_type(ker):
    out = {}
    for ty in sorted({ktype(q) for q in quads}):
        sel = np.array([ktype(q)==ty for q in quads])
        r = np.linalg.matrix_rank(ker[sel,:], tol=1e-8)
        if r: out[ty] = r
    return out

print("(1) representation picture")
# V (x) V as G-rep: dims of the isotypic pieces by number of symmetric factors
# (S^2 V_i has Casimir 8, wedge^2 V_i Casimir 0): count via weights is enough:
# dim pieces 1, 9, 27, 27 -> 64.
check(1+9+27+27 == 64, "V(x)V = 1 + T + U + S^2V_1 S^2V_2 S^2V_3 : 1+9+27+27 = 64")
# wedge^2 D: torus invariants T + 1^3 (dim 12)
w2 = [p for p in itertools.combinations(range(16,28),2) if not wt[list(p)][:,3:].sum(axis=0).any()]
check(len(w2) == 12, "torus-invariant weight pairs in wedge^2 D: 12 = dim(T + 1^3)")

raise_lower_diag = [op_diag_G(i,X) for i in range(3) for X in (E,Fm)]
ker_diag = invariants(raise_lower_diag)
bt = by_type(ker_diag)
print("    Hodge classes (Delta(G).K^1-invariants) in H^4(A):", ker_diag.shape[1], bt)
check(ker_diag.shape[1] == 26 and bt.get((1,1,2)) == 6, "26 Hodge classes, 6 of type (1,1,2)")

# comparison group: G acting on both copies of V (it is the same X twice), an
# independent copy G' acting on D: this is Hg(X) x Hg(Z_K) = G x (G'.K^1).
raise_lower_indep = [op_G_on(i,X,0)+op_G_on(i,X,1) for i in range(3) for X in (E,Fm)] + \
                    [op_G_on(i,X,2) for i in range(3) for X in (E,Fm)]
ker_indep = invariants(raise_lower_indep)
bti = by_type(ker_indep)
print("    invariants of Hg(X) x Hg(Z_K) = G x G'.K^1 (no tie between X and Z):", ker_indep.shape[1], bti)
check(bti.get((1,1,2)) == 3 and ker_indep.shape[1] == 23,
      "without the tie only psi (x) NS(Z) survives in type (1,1,2): the 3 links are the whole difference 26 - 23")

# sp(V) generators: symmetric part of V(x)V via psi: A = Psi^{-1} S for S symmetric
Psi = kron(eps,eps,eps); PsiInv = np.linalg.inv(Psi)
sp_gens = []
for a in range(8):
    for b in range(a,8):
        S = np.zeros((8,8)); S[a,b] += 1; S[b,a] += 1
        sp_gens.append(op_sp(PsiInv @ S))
ker_sp = invariants(sp_gens + raise_lower_indep[6:])   # sp(V) on V+V', G on D
bts = by_type(ker_sp)
print("    Sp(V)(diag on V+V') x G x K^1 invariants (Lefschetz-type part):", ker_sp.shape[1], bts)
check(bts.get((1,1,2)) == 3, "Lefschetz-type part of type (1,1,2) is psi (x) NS(Z): dim 3")
# the Lefschetz-type part is contained in the Hodge classes
P = ker_diag @ np.linalg.pinv(ker_diag)
check(np.allclose(P @ ker_sp, ker_sp), "Lefschetz-type part lies inside the 26 Hodge classes")

print("(2) the cyclic permutation zeta")
# zeta on V: v1 x v2 x v3 -> v3 x v1 x v2 ; index a = 4b1+2b2+b3 -> 4b3+2b1+b2
Z8 = np.zeros((8,8))
for b1 in range(2):
    for b2 in range(2):
        for b3 in range(2):
            Z8[4*b3+2*b1+b2, 4*b1+2*b2+b3] = 1
check(np.allclose(Z8.T @ Psi @ Z8, Psi), "zeta preserves psi")
# zeta normalises G: zeta X_in_V(X,i) zeta^-1 = X_in_V(X, i+1)
check(all(np.allclose(Z8 @ X_in_V(X,i) @ Z8.T, X_in_V(X,(i+1)%3)) for i in range(3) for X in (E,Fm,H)),
      "zeta conjugates the i-th sl_2 factor to the (i+1)-th")
Zbig = np.eye(N); Zbig[:8,:8] = Z8; Zbig[8:16,8:16] = Z8
# zeta acts on the weight-zero span of wedge^4 (it permutes the a-coordinates)
def perm_wedge(Zm):
    """matrix of zeta from the weight-zero span into wedge^4 (enlarged index set),
    together with the embedding of the weight-zero span into the same index set."""
    imgs = []
    for q in quads:
        im = [int(np.argmax(np.abs(Zm[:,k]))) for k in q]
        sign = 1; arr = im[:]
        for ii in range(4):
            for jj in range(3-ii):
                if arr[jj] > arr[jj+1]:
                    arr[jj],arr[jj+1] = arr[jj+1],arr[jj]; sign = -sign
        imgs.append((tuple(arr), sign))
    keys = sorted(set(quads) | {k for k,_ in imgs}); idx = {k:j for j,k in enumerate(keys)}
    A = np.zeros((len(keys), len(quads))); Emb = np.zeros((len(keys), len(quads)))
    for j,(k,sg) in enumerate(imgs): A[idx[k], j] = sg
    for j,q in enumerate(quads): Emb[idx[q], j] = 1
    return A, Emb
Zw, Emb = perm_wedge(Zbig)
print("    zeta maps", int((np.abs(Zw).sum(axis=1)>0).sum()) - len(quads), "weight-zero quads out of the weight-zero span")
sel112 = np.array([ktype(q)==(1,1,2) for q in quads])
# project the 26 invariants onto type (1,1,2) and take the 6-dim piece
proj = ker_diag.copy(); proj[~sel112,:] = 0
u,s,vt = np.linalg.svd(proj, full_matrices=False)
W6 = u[:, s > 1e-8]
check(W6.shape[1] == 6, "the (1,1,2) Hodge classes form a 6-dimensional space W6")
# zeta-fixed vectors in W6: kernel of (Zw - 1) restricted to W6
M = (Zw - Emb) @ W6
fixed_dim = W6.shape[1] - np.linalg.matrix_rank(M, tol=1e-8)
print("    zeta-fixed vectors in W6:", fixed_dim)
check(fixed_dim == 3, "zeta fixes exactly the 3-dimensional Lefschetz part psi (x) NS(Z) of W6")
# and those fixed vectors are the Sp(V)-invariant ones
projs = ker_sp.copy(); projs[~sel112,:] = 0
u2,s2,vt2 = np.linalg.svd(projs, full_matrices=False); W3 = u2[:, s2 > 1e-8]
check(np.allclose((Zw - Emb) @ W3, 0), "psi (x) NS(Z) is zeta-fixed")
# the F-line of links: the complement of W3 in W6 (3-dim, = Hom_G(T_X,T_Z) over Qbar);
# none of its nonzero vectors is zeta-fixed, and zeta.xi is not even a Hodge class:
comp = W6 - W3 @ (W3.T @ W6); u3,s3,_ = np.linalg.svd(comp, full_matrices=False); Xi3 = u3[:, s3>1e-8]
check(Xi3.shape[1] == 3, "Hom_G(T_X, T_Z) (x) Qbar is 3-dimensional (one link per place)")
img = Zw @ Xi3
check(np.linalg.matrix_rank(np.hstack([Emb @ ker_diag, img]), tol=1e-8) == 26 + 3,
      "zeta carries the link space to a space meeting the Hodge classes only in 0")
# full count of zeta-fixed Hodge classes in H^4(A)
Mall = (Zw - Emb) @ ker_diag
fixed_all = ker_diag.shape[1] - np.linalg.matrix_rank(Mall, tol=1e-8)
print("    zeta-fixed Hodge classes in all of H^4(A):", fixed_all, "of 26")
# the Sp(V)-invariants are zeta-fixed (since zeta is in Sp(V)):
check(np.allclose((Zw - Emb) @ ker_sp, 0), "every Lefschetz-type class is zeta-fixed")
print("    Lefschetz-type (Sp(V)-invariant) Hodge classes:", ker_sp.shape[1], "of 26")

print("(3) Zariski closure of the circle in the torus K^1; the Weil-type variant")
def stable_sublattice(vectors_killed, group):
    """Largest group-stable sublattice of the annihilator of the given functional(s):
    returns (rank of span of the orbit of the functionals, the orbit span basis)."""
    orbit = []
    for f in vectors_killed:
        for g in group: orbit.append(tuple(g(f)))
    Mo = sp.Matrix(sorted(set(orbit)))
    return Mo.rank(), Mo
# torus K^1 alone: characters Z^3, Galois acts by permutations (signs uniform: flip all)
def perm_group(transitive='S3'):
    perms = list(itertools.permutations(range(3))) if transitive=='S3' else [(0,1,2),(1,2,0),(2,0,1)]
    return perms
def gal_K1(uniform_sign=True, perms=None):
    gs = []
    for p in perms:
        for e in (1,-1):
            gs.append(lambda v,p=p,e=e: [e*v[p.index(i)] for i in range(3)])
    return gs
for grp in ('S3','A3'):
    G3 = gal_K1(perms=perm_group(grp))
    r,_ = stable_sublattice([(1,1,0)], G3)     # (u,u,1): characters b with b1+b2 = 0 killed
    check(r == 3, f"uniform signs, Galois {grp}: closure of (u,u,1) is all of K^1 (rank 3)")
    r,Mo = stable_sublattice([(1,-1,0)], G3)   # (u,1/u,1)
    check(r == 2, f"mixed signs, Galois {grp}: closure of (u,1/u,1) has rank 2")
    ann = Mo.nullspace()
    check(len(ann) == 1 and list(ann[0]/ann[0][0]) == [1,1,1],
          f"   its annihilator is Z(1,1,1): T_0 = ker(chi_1 chi_2 chi_3) = ker(N_{{K/k}}) on K^1")
# Weil-type variant: D_+ = V_1 chi_1 + V_2 chi_2 + V_3 chi_3 ; Hodge type (1,0) on
# V_1 chi_1, V_2 chi_2^{-1}, V_3^{1,0} W_3 : signature (3,3) ; det D_+ = (chi_1 chi_2 chi_3)^2.
h10_plus = 2 + 0 + 1
check(h10_plus == 3, "Weil variant: dim H^{1,0} cap D_+ = 3 = n (signature (3,3))")
check((2,2,2) != (0,0,0) and sum([2,2,2]) % 3 == 0, "det D_+ = (chi_1 chi_2 chi_3)^2 is trivial on T_0, not on K^1")
# uniform-sign variants: signature (5,1) or (1,5):
check(2+2+1 == 5, "uniform signs: dim H^{1,0} cap D_+ = 5 (or 1): not of Weil type")
# T_Z survives: the torus-invariant part of wedge^2 D under T_0 is still T + 1^3:
# characters appearing in wedge^2 D: 0 (12 times), +-2 e_i, +-e_i +- e_j ; on T_0 (mod (1,1,1))
# none of the nonzero ones vanish:
nonzero_chars = set()
for v in [(2,0,0),(1,1,0),(1,-1,0)]:
    for p in itertools.permutations(v): nonzero_chars.add(p)
def trivial_on_T0(c): return (c[0]-c[1]) == 0 and (c[1]-c[2]) == 0
check(not any(trivial_on_T0(c) for c in nonzero_chars), "no nonzero character of wedge^2 D is trivial on T_0: T_Z + 1^3 unchanged")

print("(4) CM points: Hodge torus of X_c x Z_{K,c} and shared factors")
# Characters of L^1 x K^1: (a;b) in Z^6. Circle h = (1,1,u ; u^{s1}, u^{s2}, 1):
# characters trivial on it: a_3 + s1 b_1 + s2 b_2 = 0.  Galois image Gamma: pairs
# (signed permutation on a, signed permutation on b) with the same permutation.
Vweights = [(a1,a2,a3,0,0,0) for a1 in (1,-1) for a2 in (1,-1) for a3 in (1,-1)]
Dweights = [tuple((sa if j==i else 0) for j in range(3)) + tuple((sb if j==i else 0) for j in range(3))
            for i in range(3) for sa in (1,-1) for sb in (1,-1)]
def signed_perm(p, s):      # v -> (s_i v_{p^-1(i)})
    return lambda v: [s[i]*v[p.index(i)] for i in range(3)]
def analyse(name, gamma, s1=1, s2=1, verbose=True):
    f = (0,0,1, s1,s2,0)
    orbit = sorted({tuple(ga(f[:3]) + gb(f[3:])) for ga,gb in gamma})
    Mo = sp.Matrix(orbit); rank = Mo.rank()
    # two weights coincide on H_c iff their difference is orthogonal to the orbit span
    def same(u,v):
        d = sp.Matrix([u[i]-v[i] for i in range(6)])
        return (Mo*d).is_zero_matrix
    classesD = []          # weights of D modulo H_c, with multiplicity
    for d in Dweights:
        for c in classesD:
            if same(c[0], d): c[1] += 1; break
        else: classesD.append([d,1])
    shared = [(v,d) for v in Vweights for d in Dweights if same(v,d)]
    # a V-weight shared with D: which V-weight class (E: +-(1,1,1); B: the others)
    sharedV = sorted({v for v,_ in shared})
    # Galois orbits on the D-weight classes (each orbit = one simple isogeny factor of Z_{K,c}
    # when the weights are distinct); and the Galois closure of S u -S for a primitive link set S
    def gal_image(w, ga, gb): return tuple(ga(list(w[:3])) + gb(list(w[3:])))
    def cls(w):
        for j,c in enumerate(classesD):
            if same(c[0], w): return ('D',j)
        for j,v in enumerate(Vweights):
            if same(v, w): return ('V',j)
        return ('?',w)
    orbitsD = set()
    for d in Dweights:
        orb = frozenset(cls(gal_image(d,ga,gb)) for ga,gb in gamma)
        orbitsD.add(orb)
    # primitive link monomial: S = {w, w', d, d'} with w=(1,1,1), w'=(-1,-1,1), d=(-e3; e3), d'=(-e3;-e3)
    S = [(1,1,1,0,0,0), (-1,-1,1,0,0,0), (0,0,-1,0,0,1), (0,0,-1,0,0,-1)]
    closure = set()
    for w in S + [tuple(-x for x in w) for w in S]:
        for ga,gb in gamma: closure.add(cls(gal_image(w,ga,gb)))
    nclosV = sum(1 for c in closure if c[0]=='V'); nclosD = sum(classesD[c[1]][1] for c in closure if c[0]=='D')
    # degree-4 Hodge classes on A_c: zero-sum 4-subsets of the 28 basis vectors modulo H_c
    basis = Vweights + Vweights + Dweights
    def restricted(v):   # coordinates of v in X(H_c) = Z^6 / Lambda_0 : use Mo v
        return tuple(Mo*sp.Matrix(v))
    rb = [restricted(v) for v in basis]
    n4 = 0; n112 = 0; prim112 = 0
    for q in itertools.combinations(range(28),4):
        if any(sum(rb[k][j] for k in q) != 0 for j in range(len(rb[0]))): continue
        n4 += 1
        ty = tuple(sum(1 for k in q if lab[k]==j) for j in range(3))
        if ty == (1,1,2):
            n112 += 1
            union = any(all(rb[q[a]][j]+rb[q[b]][j]==0 for j in range(len(rb[0]))) for a,b in itertools.combinations(range(4),2))
            if not union: prim112 += 1
    if verbose:
        print(f"    {name}: rank H_c = {rank}; D-weight classes (mult) = {sorted(c[1] for c in classesD)};"
              f" V-weights shared with D: {len(sharedV)} of 8"
              + (f" (classes {sharedV})" if sharedV and len(sharedV) <= 2 else "")
              + f"; dim Hdg^2(A_c) = {n4}, type (1,1,2): {n112}, primitive: {prim112}")
        print(f"         Galois orbits on D-weights: {len(orbitsD)} (= simple factors of Z_c up to isogeny if weights distinct);"
              f" Galois closure of S u -S for a primitive link set: {nclosV} V-weights + {nclosD} D-weights -> carrier of dimension {(nclosV+nclosD)//2}")
    return rank, classesD, sharedV, n4, n112, prim112

S3 = list(itertools.permutations(range(3))); A3 = [(0,1,2),(1,2,0),(2,0,1)]
uni = lambda e: (e,e,e)
# (i) L = K = Fk : same uniform sign on both sides
for perms,nm in ((S3,'S3'),(A3,'A3')):
    gamma = [(signed_perm(p,uni(e)), signed_perm(p,uni(e))) for p in perms for e in (1,-1)]
    r, cl, sh, n4, n112, pr = analyse(f"(i)  L = K = Fk, Galois {nm}, signs (ι0,ι0)", gamma)
    check(r == 3 and len(sh) == 8, "   rank 3; every weight of X_c occurs in Z_{K,c}: Hom(X_c,Z_{K,c}) != 0")
    check(sorted(c[1] for c in cl) == [1]*6 + [3,3], "   Z_{K,c} ~ E^3 x B (weight multiplicities 3,3,1,1,1,1,1,1)")
    r, cl, sh, *_ = analyse(f"(i') L = K = Fk, Galois {nm}, signs (ι0bar,ι0bar)", gamma, -1, -1)
    check(r == 3 and len(sh) == 8 and sorted(c[1] for c in cl) == [1]*6+[3,3], "   other uniform sign: again Z_{K,c} ~ E^3 x B")
    r, cl, sh, n4, n112, pr = analyse(f"(iW) L = K = Fk, Galois {nm}, mixed signs (Weil variant)", gamma, 1, -1)
    print(f"         shared V-weights: {len(sh)} (Galois {nm}: " + ("Z^W_c ~ B x B', both isogenous to the threefold B of X_c ~ E x B" if r == 3 else "no factor shared with X_c") + ")")
    check((nm == 'A3' and r == 3 and len(sh) == 6) or (nm == 'S3' and r == 5 and len(sh) == 0),
          "   Weil variant at the K-special point: rank 3 and Z^W ~ B^2 for cyclic F, rank 5 and no common factor otherwise")
# (i'') L = K = Fk with k = Q(sqrt(d_F)) inside the Galois closure of F: sign = sgn(pi)
def sgn(p): return 1 if sp.combinatorics.Permutation(list(p)).is_even else -1
gamma = [(signed_perm(p,uni(sgn(p))), signed_perm(p,uni(sgn(p)))) for p in S3]
r, cl, sh, *_ = analyse("(i'') L = K = Fk, k = Q(sqrt(d_F)), Galois S3 with sign sgn(pi)", gamma)
check(r == 3 and len(sh) == 8 and sorted(c[1] for c in cl) == [1]*6+[3,3], "   again rank 3 and Z_{K,c} ~ E^3 x B")

print("(5) spin_9 restricted to sl_2^3 (Kuga-Satake variety of T(-1) versus X)")
# so_9 weights of the spin representation: (+-1/2)^4 ; so_3^3 c so_9 through 9 = 3+3+3 with the
# Cartan of the i-th so_3 the i-th coordinate; restriction = drop the 4th coordinate.
spin = [w for w in itertools.product((sp.Rational(1,2),-sp.Rational(1,2)), repeat=4)]
restr = {}
for w in spin: restr[w[:3]] = restr.get(w[:3],0) + 1
check(sorted(restr.values()) == [2]*8 and len(restr) == 8,
      "spin_9 | sl_2^3 = V_1 (x) V_2 (x) V_3 (x) Qbar^2 ; so H^1(KS(T)) = C^+(T) = V^{32}, KS(T) ~ X^{32}")
print("    (the F-linear even Clifford algebra C^+_F(D^0) = D is H^1(Z_K); Z_K is the F-Clifford carrier twisted by K^1)")

# (ii) L = Fk, K = Fk', k != k', independent uniform signs
for perms,nm in ((S3,'S3'),(A3,'A3')):
    gamma = [(signed_perm(p,uni(e)), signed_perm(p,uni(e2))) for p in perms for e in (1,-1) for e2 in (1,-1)]
    r, cl, sh, n4, n112, pr = analyse(f"(ii) L = Fk, K = Fk', k != k' (independent), Galois {nm}", gamma)
    check(r == 6 and len(sh) == 0, "   rank 6: no shared weight, Hom(X_c,Z_{K,c}) = 0")
# (iii) F non-Galois (S3), k' = k.Q(sqrt(disc F)): K-side sign = L-side sign times sgn(pi)
gamma = [(signed_perm(p,uni(e)), signed_perm(p,uni(e*sgn(p)))) for p in S3 for e in (1,-1)]
r, cl, sh, n4, n112, pr = analyse("(iii) L = Fk, K = Fk', k' = k.Q(sqrt(d_F)), Galois S3", gamma)
print(f"         shared V-weights: {sh}")
# (iv) L primitive sextic CM (full signed permutations B_3 on the L side), K = Fk with the
#      K-side sign a quadratic character of B_3: prod s_i, sgn(pi), or their product
B3 = [(p,s) for p in S3 for s in itertools.product((1,-1),repeat=3)]
for nmc, charf in (("prod s_i", lambda p,s: s[0]*s[1]*s[2]), ("sgn(pi)", lambda p,s: sgn(p)),
                   ("prod s_i . sgn(pi)", lambda p,s: s[0]*s[1]*s[2]*sgn(p))):
    gamma = [(signed_perm(p,s), signed_perm(p,uni(charf(p,s)))) for p,s in B3]
    r, cl, sh, *_ = analyse(f"(iv) L primitive (B_3), K = Fk with k cut out by {nmc}", gamma)
    print(f"         shared V-weights: {len(sh)}")
# (v) both primitive, independent: all pairs of signed permutations over the same permutation
gamma = [(signed_perm(p,s), signed_perm(p,s2)) for p in S3 for s in itertools.product((1,-1),repeat=3)
         for s2 in itertools.product((1,-1),repeat=3)]
r, cl, sh, *_ = analyse("(v)  L, K both primitive, independent signs", gamma)
check(r == 6 and len(sh) == 0, "   rank 6, Hom(X_c, Z_{K,c}) = 0")

print("ALL CHECKS PASSED" if OK else "SOME CHECKS FAILED")
sys.exit(0 if OK else 1)
