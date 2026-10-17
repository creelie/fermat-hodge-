#!/usr/bin/env python3
"""
convolution_checks.py -- Route B, round 2: numerical checks in H8's formal model
(exterior algebra of H^1(A x A'), p2prime.py conventions, as in
product_object.py) for the statements of Sect. VI of the paper.

Checks
 (A) For every v in T D_{n,n} with nonzero mixed component, v _| theta_A != 0
     (the rank of v -> v _| theta_A on T D equals the number n^2-m^2-m'^2 of
     mixed directions).  Used in Proposition E (diagonal of ev_E(v)).
 (B) Hypothesis V' (secant pieces orthogonal to line-bundle pieces on the
     A-side): E = E_F (+) E_rest, and the sum of the contraction ranks into
     ch(E_F), ch(E_rest) exceeds r(gamma) by exactly the number of mixed
     directions.  Likewise under the finer hypothesis V (all cross Ext zero).
 (C) Hankel rank of the character of a subvariety Y of middle dimension on a
     very general Weil 2n-fold: c_0 = ... = c_{n-1} = 0, c_n != 0 gives
     rho = 3 and r = 7n^2 - 2n whatever the higher c_k are; the count that
     (P2') asks of O_Y.
 (D) The trace of a block matrix product (upper triangular) x (strictly upper
     triangular) is zero: the linear algebra behind Lemma A.

Run: python3 -I convolution_checks.py   (about 2 minutes; floating point ranks,
SVD with relative tolerance 1e-7; all reported ranks are integers).
"""
import itertools, math, sys
import numpy as np

rng = np.random.default_rng(7)
zeta = (-1 + 1j*np.sqrt(3))/2

class Ext:
    def __init__(self, n):
        self.n = n; self.G = 4*n
        self.mono = {}; self.basis = []
        for k in range(self.G+1):
            for c in itertools.combinations(range(self.G), k):
                self.mono[c] = len(self.basis); self.basis.append(c)
        self.N = len(self.basis)
    def e(self, j): return {(2*j,): 1.0+0j}
    def f(self, j): return {(2*j+1,): 1.0+0j}
    @staticmethod
    def add(a, b, cb=1.0):
        r = dict(a)
        for k, v in b.items(): r[k] = r.get(k, 0) + cb*v
        return {k: v for k, v in r.items() if abs(v) > 1e-12}
    @staticmethod
    def scal(a, c): return {k: c*v for k, v in a.items()}
    @staticmethod
    def wedge(a, b):
        r = {}
        for ka, va in a.items():
            sa = set(ka)
            for kb, vb in b.items():
                if sa & set(kb): continue
                arr = list(ka) + list(kb); sign = 1
                for i in range(len(arr)):
                    for j in range(len(arr)-1-i):
                        if arr[j] > arr[j+1]:
                            arr[j], arr[j+1] = arr[j+1], arr[j]; sign = -sign
                key = tuple(arr); r[key] = r.get(key, 0) + sign*va*vb
        return {k: v for k, v in r.items() if abs(v) > 1e-12}
    def contract(self, g, a):
        r = {}
        for k, v in a.items():
            if g in k:
                pos = k.index(g); key = k[:pos] + k[pos+1:]
                r[key] = r.get(key, 0) + (-1)**pos * v
        return r
    def wedge_gen(self, g, a): return self.wedge({(g,): 1.0+0j}, a)
    def vec(self, a):
        v = np.zeros(self.N, dtype=complex)
        for k, c in a.items(): v[self.mono[k]] = c
        return v
    def power(self, a, k):
        r = {(): 1.0+0j}
        for _ in range(k): r = self.wedge(r, a)
        return r
    def exp(self, a, top):
        r = {(): 1.0+0j}; term = {(): 1.0+0j}
        for k in range(1, top+1):
            term = self.scal(self.wedge(term, a), 1.0/k); r = self.add(r, term)
        return r

def rank(M, tol=1e-7):
    M = np.asarray(M)
    if M.size == 0: return 0
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > tol*s[0]).sum()) if s[0] > 0 else 0

def ops(X):
    n = X.n
    w = [2*j+1 for j in range(n)] + [2*j for j in range(n, 2*n)]   # H^{0,1}
    c = [2*j for j in range(n)] + [2*j+1 for j in range(n, 2*n)]   # T
    return w, c

def apply_op(X, op, a):
    kind, g = op
    return X.wedge_gen(g, a) if kind == 'w' else X.contract(g, a)

def h1T_ops(X):
    w, c = ops(X)
    return [(('w', a), ('c', v)) for a in w for v in c]

def ht2_ops(X):
    w, c = ops(X)
    o = [('w', g) for g in w] + [('c', g) for g in c]
    return [(o[i], o[j]) for i in range(len(o)) for j in range(i+1, len(o))]

def cmat(X, gamma, op_list):
    rows = []
    for o in op_list:
        a = gamma
        for op in o: a = apply_op(X, op, a)
        rows.append(X.vec(a))
    return np.array(rows)

def ann_dim(X, gammas, op_list):
    M = np.hstack([cmat(X, g, op_list) for g in gammas])
    return len(op_list) - rank(M)

def contraction_rank(X, gamma, op_list):
    return rank(cmat(X, gamma, op_list))

def hankel_rank(cs, n):
    mu = [math.factorial(k)*cs[k] for k in range(2*n+1)]
    H = np.array([[mu[j+i] for i in range(3)] for j in range(2*n-1)], dtype=complex)
    return rank(H)

def run(n, m):
    mp = n - m
    X = Ext(n)
    IA = list(range(m)) + list(range(n, n+m)); IB = [j for j in range(2*n) if j not in IA]
    def theta(I):
        t = {}
        for j in I: t = X.add(t, X.wedge(X.e(j), X.f(j)), 1j*(1 if j < n else -1))
        return t
    def om(I, plus):
        r = {(): 1.0+0j}
        for j in I: r = X.wedge(r, X.e(j) if plus else X.f(j))
        return r
    thA, thB = theta(IA), theta(IB); th = X.add(thA, thB)
    opA, omA, opB, omB = om(IA, True), om(IA, False), om(IB, True), om(IB, False)
    H1T = h1T_ops(X); HT2 = ht2_ops(X)
    print(f"\n=== n={n}: A (Weil {2*m}-fold) x A' (Weil {2*mp}-fold); dim H^1(T)={len(H1T)}, dim HT^2={len(HT2)} ===")
    Wp, Wm = X.wedge(opA, opB), X.wedge(omA, omB)
    # T D_{n,n} as a subspace of H^1(T): kernel of contraction into theta, W_+, W_-
    M = np.hstack([cmat(X, g, H1T) for g in (th, Wp, Wm)])
    # left null space of M (rows indexed by H^1(T) ops): economy SVD, U is square of size dim H^1(T)
    U, S, Vh = np.linalg.svd(M, full_matrices=False)
    rk = int((S > 1e-7*S[0]).sum())
    TD = U[:, rk:].conj().T          # basis of {x : x @ M = 0}
    print(f"dim T D_(n,n) = {TD.shape[0]} [n^2 = {n*n}]")
    blockA = [k for k, o in enumerate(H1T) if o[0][1]//2 in IA and o[1][1]//2 in IA]
    blockB = [k for k, o in enumerate(H1T) if o[0][1]//2 in IB and o[1][1]//2 in IB]
    mixed_idx = [k for k in range(len(H1T)) if k not in blockA and k not in blockB]
    # (A): rank of v -> v _| theta_A on T D
    CA = cmat(X, thA, H1T)
    r_thA = rank(TD @ CA)
    n_mixed = n*n - ann_dim(X, [thA, opA, omA], [H1T[k] for k in blockA]) - ann_dim(X, [thB, opB, omB], [H1T[k] for k in blockB])
    print(f"(A) rank of (v -> v _| theta_A) on T D = {r_thA}; number of mixed directions n^2-m^2-m'^2 = {n_mixed}")
    # the block-diagonal part of T D kills theta_A, so the rank equals the dimension of the mixed part:
    print(f"    => every v in T D with nonzero mixed component has v _| theta_A != 0: {r_thA == n_mixed}")

    # classes of the pieces (K = Q(zeta_3) twist as in round 1)
    u, up = rng.normal()+1j*rng.normal(), rng.normal()+1j*rng.normal()
    def weil(opl, oml, uu, lam): return X.add(X.scal(opl, lam*uu), X.scal(oml, np.conj(lam*uu)))
    wA1, wA2 = weil(opA, omA, u, 1), weil(opA, omA, u, zeta**(2*m))
    b = 1 if (2*m - 2*mp) % 3 == 0 else -1
    wB1, wB2 = weil(opB, omB, up, 1), weil(opB, omB, up, zeta**(2*mp*b))
    pA = [{} , {}]; pB = [{}, {}]
    for i in range(2):
        for k in range(2*m+1): pA[i] = X.add(pA[i], X.power(thA, k), rng.normal())
        for k in range(2*mp+1): pB[i] = X.add(pB[i], X.power(thB, k), rng.normal())
    chF = [X.add(wA1, pA[0]), X.add(wA2, pA[1])]          # N_i = 1
    chG = [X.add(wB1, pB[0]), X.add(wB2, pB[1])]          # N'_j = 1
    a = {(0,0): 1.0, (1,1): -1.0}                          # twisted difference: w = chF1 chG1 - chF2 chG2 (Weil part)
    # Summands according to which Ext groups vanish.
    #   E_{FG}  : pieces F_i x G'_j                 ch = sum a_ij chF_i chG_j
    #   E_{FL'} : pieces F_i x L'^k (cancel omega_i x q'_i), ch = - sum_i chF_i x q'_i, q'_i = sum_j a_ij p'_j
    #   E_{LG'} : pieces L^l x G'_j,                 ch = - sum_j q_j x chG_j, q_j = sum_i a_ij p_i
    #   E_{LL'} : line bundles L^l x L'^k and (L x L')^k, ch = gamma - (sum of the above)
    E_FG = {}; E_FLp = {}; E_LGp = {}
    for (i, j), aij in a.items():
        E_FG = X.add(E_FG, X.wedge(chF[i], chG[j]), aij)
    for i in range(2):
        qpi = {}
        for j in range(2):
            if (i, j) in a: qpi = X.add(qpi, pB[j], a[(i, j)])
        E_FLp = X.add(E_FLp, X.wedge(chF[i], qpi), -1.0)
    for j in range(2):
        qj = {}
        for i in range(2):
            if (i, j) in a: qj = X.add(qj, pA[i], a[(i, j)])
        E_LGp = X.add(E_LGp, X.wedge(qj, chG[j]), -1.0)
    partial = X.add(X.add(E_FG, E_FLp), E_LGp)
    # Weil part of partial and its polynomial junk
    v0 = X.vec(partial)
    iWp, iWm = X.mono[tuple(sorted(2*j for j in range(2*n)))], X.mono[tuple(sorted(2*j+1 for j in range(2*n)))]
    polyAB = np.array([X.vec(X.wedge(X.power(thA, k), X.power(thB, l))) for k in range(2*m+1) for l in range(2*mp+1)]).T
    coef, *_ = np.linalg.lstsq(polyAB, v0, rcond=None)
    rem = v0 - polyAB @ coef
    print(f"(B) ch(E_FG)+ch(E_FL')+ch(E_LG') = N w + s_2 with s_2 in Q[th_A] x Q[th_A']: residual outside = {np.linalg.norm(np.delete(rem, [iWp, iWm])):.1e}, |Nw| = {abs(rem[iWp]):.3f}")
    mult = rng.normal(size=3)
    E_LLp = {}
    for k in range(2*m+1):
        for l in range(2*mp+1):
            E_LLp = X.add(E_LLp, X.wedge(X.power(thA, k), X.power(thB, l)), -coef[k*(2*mp+1)+l])
    for k, mu_ in zip((0, 1, 2), mult): E_LLp = X.add(E_LLp, X.exp(X.scal(th, k), 2*n), mu_)
    gamma = X.add(partial, E_LLp)
    cs = [sum(mu_*k**j/math.factorial(j) for k, mu_ in zip((0, 1, 2), mult)) for j in range(2*n+1)]
    rho = hankel_rank(cs, n)
    annG = ann_dim(X, [gamma], HT2); r = len(HT2) - annG
    print(f"    gamma = ch(E): rho = {rho}, dim Ann_HT2(gamma) = {annG} [n^2 = {n*n}], r(gamma) = {r} [(4+rho)n^2-2n = {(4+rho)*n*n-2*n}]")
    # Hypothesis V': E = E_F (+) E_rest, E_F = E_FG + E_FL', E_rest = E_LG' + E_LL'
    E_F = X.add(E_FG, E_FLp); E_rest = X.add(E_LGp, E_LLp)
    for name, parts in [("V' (Ext(F_i,L^l)=0 both ways): E_F (+) E_rest", [E_F, E_rest]),
                        ("V'' (Ext(G'_j,L'^k)=0 both ways): E_G (+) E_rest'", [X.add(E_FG, E_LGp), X.add(E_FLp, E_LLp)]),
                        ("V (all cross Ext zero): four summands", [E_FG, E_FLp, E_LGp, E_LLp])]:
        ranks = [contraction_rank(X, g, HT2) for g in parts]
        common = ann_dim(X, parts, HT2)
        print(f"    {name}: contraction ranks {ranks}, sum = {sum(ranks)}; dim HT^2 - dim(common annihilator) = {len(HT2)-common}; "
              f"excess over r: {sum(ranks)-r} (sum of ranks), {len(HT2)-common-r} (common annihilator); mixed directions = {n_mixed}")
    # hypothesis V' but with a_ij full (all four F_i x G'_j), to see the dependence on a
    return dict(n=n, r=r, rho=rho, mixed=n_mixed)

def prym_shape():
    print("\n=== (C) the character of a middle-dimensional subvariety Y on a very general Weil 2n-fold ===")
    for n in (2, 3, 4, 5):
        for trial in range(3):
            cs = [0.0]*n + [1.0 + rng.normal()] + list(rng.normal(size=n))
            if trial == 2: cs = [0.0]*n + [1.0] + [0.0]*n      # ch(O_Y) = [Y] only
            rho = hankel_rank(cs, n)
            print(f"  n={n}: c_0..c_{n-1}=0, c_n={cs[n]:.3f}, higher c generic={trial<2}: rho = {rho}, r = (4+rho)n^2-2n = {(4+rho)*n*n-2*n}; 7n^2-2n = {7*n*n-2*n}")
        print(f"  n={n}: for Y smooth, Ext^2(O_Y,O_Y) has dim <= h^2(O_Y)+h^1(N_Y)+h^0(wedge^2 N_Y); the count r = 7n^2-2n = {7*n*n-2*n} "
              f"= C(2n,2) + 3n^2 + C(2n,2) = {math.comb(2*n,2)} + {3*n*n} + {math.comb(2*n,2)} = {2*math.comb(2*n,2)+3*n*n}  "
              f"[matches: {7*n*n-2*n == 2*math.comb(2*n,2)+3*n*n}]")

def trace_check():
    print("\n=== (D) trace of (upper triangular) x (strictly upper triangular) block matrix vanishes ===")
    sizes = [2, 3, 1, 4]; N = len(sizes); off = np.cumsum([0]+sizes)
    def blocks(strict):
        M = np.zeros((off[-1], off[-1]), dtype=complex)
        for a in range(N):
            for b in range(a+1 if strict else a, N):
                M[off[a]:off[a+1], off[b]:off[b+1]] = rng.normal(size=(sizes[a], sizes[b])) + 1j*rng.normal(size=(sizes[a], sizes[b]))
        return M
    U = blocks(False); S = blocks(True)
    for p in range(4):
        print(f"  tr(U^{p} S) = {abs(np.trace(np.linalg.matrix_power(U, p) @ S)):.1e}; tr(S U^{p}) = {abs(np.trace(S @ np.linalg.matrix_power(U, p))):.1e}")

if __name__ == "__main__":
    out = [run(3, 2), run(4, 2)]
    prym_shape(); trace_check()
    print("\nsummary:", out)
