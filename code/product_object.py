#!/usr/bin/env python3
"""
product_object.py -- Route B: an object with the polarised Chern
character at a product point A x A' of the Weil family, and the first-order
test of the four (n=3) / eight (n=4) mixed directions.

Model: H8's (p2prime.py).  H^1 has basis e_j, f_j, j = 0..2n-1; e_j in V_+,
f_j in V_-, complex conjugation e_j <-> f_j.  H^{1,0} = <e_j (j<n), f_j (j>=n)>.
theta = i sum_j s_j e_j f_j, s_j = +1 (j<n), -1 (j>=n).
omega_+ = e_0...e_{2n-1}, omega_- = f_0...f_{2n-1}.
Product A x A': A has indices I_A = {0..m-1} u {n..n+m-1}, A' the rest
(m + m' = n), theta_A, omega_pm(A) etc. built on these indices.
K = Q(zeta_3): zeta_* acts on V_+ by zeta, on V_- by conj(zeta).

HT^1 = H^{0,1} (+) T acts by wedging f_j (j<n), e_j (j>=n) and contracting
e_j (j<n), f_j (j>=n) (dual to H^{1,0}).  HT^2 = products of two of these.

Everything is floating-point complex linear algebra (ranks of matrices with
entries in Q(i, sqrt-3) scaled by random generic data); all ranks are integers
and were stable under rerandomisation.  These are numerical checks of
statements proved by hand in Sect. VI of the paper.
"""
import itertools, sys
import numpy as np

rng = np.random.default_rng(1)
zeta = (-1 + 1j*np.sqrt(3))/2

class Ext:
    """exterior algebra on 4n generators; gen index: e_j -> 2j, f_j -> 2j+1"""
    def __init__(self, n):
        self.n = n; self.G = 4*n
        self.mono = {}
        self.basis = []
        for k in range(self.G+1):
            for c in itertools.combinations(range(self.G), k):
                self.mono[c] = len(self.basis); self.basis.append(c)
        self.N = len(self.basis)
    def e(self, j): return {(2*j,): 1.0+0j}
    def f(self, j): return {(2*j+1,): 1.0+0j}
    @staticmethod
    def add(a, b, cb=1.0):
        r = dict(a)
        for k, v in b.items():
            r[k] = r.get(k, 0) + cb*v
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
                seq = list(ka) + list(kb)
                # sign of sorting permutation
                sign = 1
                arr = seq[:]
                for i in range(len(arr)):
                    for j in range(len(arr)-1-i):
                        if arr[j] > arr[j+1]:
                            arr[j], arr[j+1] = arr[j+1], arr[j]; sign = -sign
                key = tuple(arr)
                r[key] = r.get(key, 0) + sign*va*vb
        return {k: v for k, v in r.items() if abs(v) > 1e-12}
    def contract(self, g, a):
        """interior product by the dual of generator g (derivation of degree -1)"""
        r = {}
        for k, v in a.items():
            if g in k:
                pos = k.index(g)
                key = k[:pos] + k[pos+1:]
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
            term = self.scal(self.wedge(term, a), 1.0/k)
            r = self.add(r, term)
        return r

def rank(vectors, tol=1e-7):
    M = np.array(vectors)
    if M.size == 0: return 0
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > tol*s[0]).sum()) if s[0] > 0 else 0

def setup(n, m):
    """return algebra, index sets, theta's, omega's for A (m) x A' (n-m)"""
    X = Ext(n)
    IA = list(range(m)) + list(range(n, n+m))
    IB = [j for j in range(2*n) if j not in IA]
    def theta(I):
        t = {}
        for j in I:
            s = 1 if j < n else -1
            t = X.add(t, X.wedge(X.e(j), X.f(j)), 1j*s)
        return t
    def om(I, plus):
        r = {(): 1.0+0j}
        for j in I: r = X.wedge(r, X.e(j) if plus else X.f(j))
        return r
    return X, IA, IB, theta, om

def ops(X):
    n = X.n
    wedge_gens = [2*j+1 for j in range(n)] + [2*j for j in range(n, 2*n)]   # H^{0,1}
    contr_gens = [2*j for j in range(n)] + [2*j+1 for j in range(n, 2*n)]   # T = (H^{1,0})^*
    return wedge_gens, contr_gens

def apply_op(X, op, a):
    kind, g = op
    return X.wedge_gen(g, a) if kind == 'w' else X.contract(g, a)

def ht1_ops(X):
    w, c = ops(X)
    return [('w', g) for g in w] + [('c', g) for g in c]

def h1T_ops(X):
    """H^1(T) = H^{0,1} (x) T: alpha wedge, v contract"""
    w, c = ops(X)
    return [(('w', a), ('c', v)) for a in w for v in c]

def contraction_matrix(X, gamma, op_list):
    rows = []
    for o in op_list:
        a = gamma
        for op in o: a = apply_op(X, op, a)
        rows.append(X.vec(a))
    return np.array(rows)

def ann_dim(X, gammas, op_list):
    """dimension of the common annihilator of the classes gammas in span(op_list)"""
    M = np.hstack([contraction_matrix(X, g, op_list) for g in gammas])
    return len(op_list) - rank(M)

def ht2_ops(X):
    o = ht1_ops(X)
    return [(o[i], o[j]) for i in range(len(o)) for j in range(i+1, len(o))]

def hankel_rank(cs, n):
    mu = [np.math.factorial(k)*cs[k] for k in range(2*n+1)] if hasattr(np, 'math') else None
    import math
    mu = [math.factorial(k)*cs[k] for k in range(2*n+1)]
    H = np.array([[mu[j+i] for i in range(3)] for j in range(2*n-1)], dtype=complex)
    return rank(H)

def run(n, m):
    import math
    mp = n - m
    X, IA, IB, theta, om = setup(n, m)
    thA, thB = theta(IA), theta(IB)
    th = X.add(thA, thB)
    opA, omA = om(IA, True), om(IA, False)
    opB, omB = om(IB, True), om(IB, False)
    u, up = rng.normal()+1j*rng.normal(), rng.normal()+1j*rng.normal()
    # rational Weil classes of the factors: omega_1 = u om_+ + conj(u) om_-,
    # omega_2 = zeta_* omega_1 : zeta_* acts on Lambda^{2m}V_+ by zeta^{2m}
    def weil(I, opl, oml, uu, mm):
        w1 = X.add(X.scal(opl, uu), X.scal(oml, np.conj(uu)))
        w2 = X.add(X.scal(opl, zeta**(2*mm)*uu), X.scal(oml, np.conj(zeta**(2*mm)*uu)))
        return w1, w2
    wA1, wA2 = weil(IA, opA, omA, u, m)
    wB1, wB2 = weil(IB, opB, omB, up, mp)
    # the Weil plane of the product
    W_plus = X.wedge(opA, opB); W_minus = X.wedge(omA, omB)
    H1T = h1T_ops(X); HT2 = ht2_ops(X)
    print(f"=== n={n}: product of Weil {2*m}-fold A and Weil {2*mp}-fold A' ===")
    print(f"dim H^1(T) = {len(H1T)}, dim HT^2 = {len(HT2)}")
    TD = ann_dim(X, [th, W_plus, W_minus], H1T)
    print(f"dim T D_(n,n) (annihilator of theta and the Weil plane in H^1(T)) = {TD}  [expect n^2 = {n*n}]")
    # product-locus tangent: block-diagonal deformations preserving each factor's theta and Weil plane
    blockA = [(('w', a), ('c', v)) for a in ops(X)[0] for v in ops(X)[1] if a//2 in IA and v//2 in IA]
    blockB = [(('w', a), ('c', v)) for a in ops(X)[0] for v in ops(X)[1] if a//2 in IB and v//2 in IB]
    TA = ann_dim(X, [thA, opA, omA], blockA); TB = ann_dim(X, [thB, opB, omB], blockB)
    print(f"dim T(product locus) = {TA} + {TB} = {TA+TB}; mixed directions in T D = {n*n - TA - TB}")
    # generic polynomial parts p(theta_A), p'(theta_B) with the top degrees
    N, Np = 1.0, 1.0
    cA = rng.normal(size=2*m+1); cB = rng.normal(size=2*mp+1)
    pA = {}; pB = {}
    for k in range(2*m+1): pA = X.add(pA, X.power(thA, k), cA[k])
    for k in range(2*mp+1): pB = X.add(pB, X.power(thB, k), cB[k])
    chF = X.add(X.scal(wA1, N), pA)
    chF2 = X.add(X.scal(wA2, N), pA)           # zeta_* F
    chG = X.add(X.scal(wB1, Np), pB)
    chG2 = X.add(X.scal(wB2, Np), pB)
    # (1) the naive exterior product F boxtimes G
    g_naive = X.wedge(chF, chG)
    a = ann_dim(X, [g_naive], H1T)
    a_pol = ann_dim(X, [g_naive, th], H1T)
    a_TD = ann_dim(X, [g_naive, th, W_plus, W_minus], H1T)
    print(f"first-order Hodge locus of ch(F boxtimes G) in H^1(T): {a}; keeping theta too: {a_pol}; inside T D_(n,n): {a_TD}  [product locus has {TA+TB}]")
    # same for the twisted difference before the polynomial cancellations (computed below) and for a pure Weil x Weil class
    print(f"   inside T D: Hodge locus of omega_1(A) x omega_1(A') = {ann_dim(X, [X.wedge(wA1, wB1), th, W_plus, W_minus], H1T)}, of omega_1(A) x p' = {ann_dim(X, [X.wedge(wA1, pB), th, W_plus, W_minus], H1T)}, of p x omega_1(A') = {ann_dim(X, [X.wedge(pA, wB1), th, W_plus, W_minus], H1T)}")
    # which of its components obstruct: wedge of Weil x polynomial parts
    for name, cls in [("omega_1(A) x p'(theta')", X.wedge(wA1, pB)),
                      ("p(theta) x omega_1(A')", X.wedge(pA, wB1)),
                      ("omega_1(A) x omega_1(A')", X.wedge(wA1, wB1)),
                      ("p x p'", X.wedge(pA, pB))]:
        print(f"   Hodge locus in H^1(T) of {name}: {ann_dim(X, [cls], H1T)}")
    # (2) the twisted difference  E_0 = F x G  (+)  (zeta_* F x zeta^{+-1}_* G)[1]
    # choose the sign of the twist on A' so that the cross terms cancel:
    # (zeta^a, zeta^b)_* acts on om_+ x om'_+ by zeta^{2ma+2m'b}, on om_+ x om'_- by zeta^{2ma-2m'b}
    for b in (1, -1):
        e_cross = (2*m*1 - 2*mp*b) % 3
        e_weil = (2*m*1 + 2*mp*b) % 3
        print(f"   twist (zeta, zeta^{b:+d}): exponent on W = {e_weil}, on cross terms = {e_cross}")
    b = 1 if (2*m - 2*mp) % 3 == 0 else -1
    assert (2*m + 2*mp*b) % 3 != 0
    def weil_twist(I, opl, oml, uu, mm, bb):
        lam = zeta**(2*mm*bb)
        return X.add(X.scal(opl, lam*uu), X.scal(oml, np.conj(lam*uu)))
    wB2 = weil_twist(IB, opB, omB, up, mp, b)
    chG2 = X.add(X.scal(wB2, Np), pB)
    g0 = X.add(X.wedge(chF, chG), X.wedge(chF2, chG2), -1.0)
    # decompose: Weil part = component on W_plus, W_minus; the rest
    v0 = X.vec(g0)
    iWp, iWm = X.mono[tuple(sorted([2*j for j in range(2*n)]))], X.mono[tuple(sorted([2*j+1 for j in range(2*n)]))]
    print(f"ch(E_0): coefficient on omega_+ = {v0[iWp]:.4f}, on omega_- = {v0[iWm]:.4f}")
    # cross terms om_+(A) om_-(A') etc. should vanish
    cross1 = X.vec(X.wedge(opA, omB)); cross2 = X.vec(X.wedge(omA, opB))
    print(f"   cross-term coefficients: {abs(v0 @ cross1.conj())/np.linalg.norm(cross1)**2:.2e}, {abs(v0 @ cross2.conj())/np.linalg.norm(cross2)**2:.2e}")
    # (3) cancel omega_i x p' and p x omega'_j by F_i x (line bundle combos) and (line bundle combos) x G_j,
    # then cancel Q[theta_A] x Q[theta_B] by line bundles on the product: here we simply subtract the
    # classes, which is what the objects do (Vandermonde solvability is checked separately below)
    g1 = X.add(g0, X.wedge(X.scal(wA1, N), pB), -1.0)         # from F x G'_1 with ch(G'_1) = -p'  (the p x p' it adds is in Q[thA] x Q[thB])
    g1 = X.add(g1, X.wedge(X.scal(wA2, N), pB), +1.0)         # from zeta_*F x G'_2 with ch = +p'
    g1 = X.add(g1, X.wedge(pA, X.scal(wB1, Np)), -1.0)
    g1 = X.add(g1, X.wedge(pA, X.scal(wB2, Np)), +1.0)
    # remove everything in Q[theta_A] (x) Q[theta_B]: project onto the complement
    polyAB = [X.vec(X.wedge(X.power(thA, k), X.power(thB, l))) for k in range(2*m+1) for l in range(2*mp+1)]
    P = np.array(polyAB).T
    coef, *_ = np.linalg.lstsq(P, X.vec(g1), rcond=None)
    rem = X.vec(g1) - P @ coef
    g_weil = {X.basis[i]: rem[i] for i in np.nonzero(np.abs(rem) > 1e-9)[0]}
    print(f"after cancellations: ch lies in span(omega_+, omega_-)? residual outside = "
          f"{np.linalg.norm(np.delete(rem, [iWp, iWm])):.2e}; "
          f"Weil coefficient |N w| = {abs(rem[iWp]):.4f}")
    # Vandermonde: e^{k theta}, k = 0..2m, span the polynomials in theta of degree <= 2m
    import math
    V = np.array([[k**j/math.factorial(j) for j in range(2*m+1)] for k in range(2*m+1)], dtype=float)
    print(f"Vandermonde det (k^j/j!, k,j=0..{2*m}) = {np.linalg.det(V):.4g} (nonzero: line bundles L^k span Q[theta_A]/theta^{2*m+1})")
    # (4) final object: add line bundles e^{k theta} on the product, k = 0,1,2, generic multiplicities
    ks = [0, 1, 2]; mult = rng.normal(size=3)
    g_final = dict(g_weil)
    for k, mu_ in zip(ks, mult): g_final = X.add(g_final, X.exp(X.scal(th, k), 2*n), mu_)
    cs = [sum(mu_*k**j/math.factorial(j) for k, mu_ in zip(ks, mult)) for j in range(2*n+1)]
    rho = hankel_rank(cs, n)
    aH = ann_dim(X, [g_final], H1T)
    A2 = ann_dim(X, [g_final], HT2)
    r = len(HT2) - A2
    print(f"final ch(E) = N w + sum_k c_k theta^k: Hankel rank rho = {rho}; "
          f"first-order Hodge locus in H^1(T) = {aH} [= n^2 = {n*n}?]; dim Ann_HT2 = {A2} [= n^2(4-rho) = {n*n*(4-rho)}]; "
          f"r(gamma) = {r} [= (4+rho)n^2-2n = {(4+rho)*n*n-2*n}]")
    return dict(n=n, TD=TD, Tprod=TA+TB, naive=a, rho=rho, aH=aH, r=r)

if __name__ == "__main__":
    res = [run(3, 2), run(4, 2)]
    print(res)
