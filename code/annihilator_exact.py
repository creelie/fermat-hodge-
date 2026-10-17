#!/usr/bin/env python3
"""
exact_model.py -- exact arithmetic (field Q(sqrt(-D)), D=3 default) version of the
exterior-algebra model of H^*(A x A') (conventions of product_object.py), and the
checks behind Theorem A of report.md:

  (1) dim T D_{n,n} = n^2, dim T(product locus) = m^2 + m'^2;
  (2) ch(E') = M w + sum_i (M/N_i) p_i(theta_A) (x) (sum_j a_ij omega'_j), i.e. the
      polynomial-cross part s' of the F-pieces is exactly zero (Lemma 2 of the report);
  (3) the annihilator of ch(E') inside T D_{n,n} is the block-diagonal part, of
      dimension m^2 + m'^2, so dim HT^2 - dim(Ann ch E' cap Ann ch E'') = r + 2mm';
  (4) the same for every single k-component theta_A^k (x) R_k, k>=1 (the proof of
      Theorem A needs only one such component).
All ranks are exact (fraction-free Gaussian elimination over Q(sqrt(-D))).
Usage: python3 -I exact_model.py [n m D]      default 3 2 3  (n=4 m=2 takes minutes)
"""
import itertools, sys, math
from fractions import Fraction as Fr

D = 3
class K:
    """a + b*sqrt(-D), a,b rational"""
    __slots__ = ("a", "b")
    def __init__(self, a, b=0): self.a = Fr(a); self.b = Fr(b)
    def __add__(s, o): o = K._c(o); return K(s.a+o.a, s.b+o.b)
    __radd__ = __add__
    def __sub__(s, o): o = K._c(o); return K(s.a-o.a, s.b-o.b)
    def __neg__(s): return K(-s.a, -s.b)
    def __mul__(s, o): o = K._c(o); return K(s.a*o.a - D*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def conj(s): return K(s.a, -s.b)
    def norm(s): return s.a*s.a + D*s.b*s.b
    def inv(s): n = s.norm(); return K(s.a/n, -s.b/n)
    def __truediv__(s, o): return s * K._c(o).inv()
    def iszero(s): return s.a == 0 and s.b == 0
    def __eq__(s, o): o = K._c(o); return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def __repr__(s): return f"({s.a}+{s.b}r)" if s.b else f"{s.a}"
    @staticmethod
    def _c(o): return o if isinstance(o, K) else K(o)
ONE = K(1); ZERO = K(0); RT = K(0, 1)   # RT = sqrt(-D)

class Ext:
    def __init__(self, n):
        self.n = n; self.G = 4*n
    def e(self, j): return {(2*j,): ONE}
    def f(self, j): return {(2*j+1,): ONE}
    @staticmethod
    def add(a, b, cb=ONE):
        r = dict(a)
        for k, v in b.items():
            r[k] = r.get(k, ZERO) + cb*v
        return {k: v for k, v in r.items() if not v.iszero()}
    @staticmethod
    def scal(a, c): return {k: c*v for k, v in a.items()}
    @staticmethod
    def wedge(a, b):
        r = {}
        for ka, va in a.items():
            sa = set(ka)
            for kb, vb in b.items():
                if sa & set(kb): continue
                arr = list(ka)+list(kb); sign = 1
                for i in range(len(arr)):
                    for j in range(len(arr)-1-i):
                        if arr[j] > arr[j+1]:
                            arr[j], arr[j+1] = arr[j+1], arr[j]; sign = -sign
                key = tuple(arr); r[key] = r.get(key, ZERO) + (va*vb if sign > 0 else -(va*vb))
        return {k: v for k, v in r.items() if not v.iszero()}
    def contract(self, g, a):
        r = {}
        for k, v in a.items():
            if g in k:
                pos = k.index(g); key = k[:pos]+k[pos+1:]
                r[key] = r.get(key, ZERO) + (v if pos % 2 == 0 else -v)
        return {k: v for k, v in r.items() if not v.iszero()}
    def wedge_gen(self, g, a): return self.wedge({(g,): ONE}, a)
    def power(self, a, k):
        r = {(): ONE}
        for _ in range(k): r = self.wedge(r, a)
        return r

def rank_exact(rows):
    """rows: list of dicts {colkey: K}; exact rank by Gaussian elimination"""
    rows = [dict(r) for r in rows if r]
    rk = 0
    while rows:
        piv = rows.pop()
        if not piv: continue
        rk += 1
        c = next(iter(piv)); pc = piv[c]
        new = []
        for r in rows:
            if c in r:
                f = r[c] / pc
                for k, v in piv.items():
                    r[k] = r.get(k, ZERO) - f*v
                r = {k: v for k, v in r.items() if not v.iszero()}
            if r: new.append(r)
        rows = new
    return rk

def ops(X):
    n = X.n
    wedge_gens = [2*j+1 for j in range(n)] + [2*j for j in range(n, 2*n)]   # H^{0,1}
    contr_gens = [2*j for j in range(n)] + [2*j+1 for j in range(n, 2*n)]   # T = (H^{1,0})^*
    return wedge_gens, contr_gens
def h1T_ops(X):
    w, c = ops(X); return [(a, v) for a in w for v in c]
def apply(X, op, a):
    return X.wedge_gen(op[0], X.contract(op[1], a))
def tagged(a, tag): return {(tag,)+k: v for k, v in a.items()}
def ann_dim(X, gammas, op_list):
    rows = []
    for o in op_list:
        row = {}
        for t, g in enumerate(gammas): row.update(tagged(apply(X, o, g), t))
        rows.append(row)
    return len(op_list) - rank_exact(rows)

def run(n, m):
    mp = n - m
    X = Ext(n)
    IA = list(range(m)) + list(range(n, n+m)); IB = [j for j in range(2*n) if j not in IA]
    def theta(I):   # theta = i sum s_j e_j f_j ; we drop the factor i (irrelevant for all ranks, keeps us in Q(sqrt-D))
        t = {}
        for j in I: t = X.add(t, X.wedge(X.e(j), X.f(j)), ONE if j < n else -ONE)
        return t
    def om(I, plus):
        r = {(): ONE}
        for j in I: r = X.wedge(r, X.e(j) if plus else X.f(j))
        return r
    thA, thB = theta(IA), theta(IB); th = X.add(thA, thB)
    opA, omA, opB, omB = om(IA, True), om(IA, False), om(IB, True), om(IB, False)
    H1T = h1T_ops(X)
    blockA = [o for o in H1T if o[0]//2 in IA and o[1]//2 in IA]
    blockB = [o for o in H1T if o[0]//2 in IB and o[1]//2 in IB]
    print(f"=== n={n}, (m,m')=({m},{mp}), field Q(sqrt(-{D})) ===")
    TD = ann_dim(X, [th, X.wedge(opA, opB), X.wedge(omA, omB)], H1T)
    TA = ann_dim(X, [thA, opA, omA], blockA); TB = ann_dim(X, [thB, opB, omB], blockB)
    print(f"(1) dim T D_(n,n) = {TD} [n^2={n*n}];  dim T(product locus) = {TA}+{TB} = {TA+TB};  mixed = {TD-TA-TB} [2mm'={2*m*mp}]")
    # rational Weil bases: omega_1 = u om_+ + conj(u) om_-, omega_2 = sqrt(-D) u om_+ + conj(.) om_-
    def weil(opl, oml, uu):
        return (X.add(X.scal(opl, uu), X.scal(oml, uu.conj())),
                X.add(X.scal(opl, RT*uu), X.scal(oml, (RT*uu).conj())))
    u = K(2, 1); up = K(1, -3)
    wA = weil(opA, omA, u); wB = weil(opB, omB, up)
    # polynomial parts p_i, p'_j with arbitrary nonzero rational coefficients (positive degree)
    cA = [[1, 2, -1, 3, 1], [2, -1, 1, 1, -2]][:]; cB = [[1, 1, 3, -2, 1], [3, 2, -1, 1, 1]]
    pA = [{}, {}]; pB = [{}, {}]
    for i in range(2):
        for k in range(2*m+1): pA[i] = X.add(pA[i], X.power(thA, k), K(cA[i][k]))
        for k in range(2*mp+1): pB[i] = X.add(pB[i], X.power(thB, k), K(cB[i][k]))
    N = [K(1), K(1)]; Np = [K(1), K(1)]
    chF = [X.add(X.scal(wA[i], N[i]), pA[i]) for i in range(2)]
    chG = [X.add(X.scal(wB[j], Np[j]), pB[j]) for j in range(2)]
    # a rational element of W(A x A'): x om_+om'_+ + conj(x) om_-om'_-  ==>  a_ij
    # om_+om'_+ in terms of omega_i (x) omega'_j: solve 2x2 systems
    # omega_1 = u P + ub Mi, omega_2 = ru P + conj(ru) Mi  (P=om_+, Mi=om_-); invert
    def inv2(a, b, c, d):
        det = a*d - b*c; return (d/det, -b/det, -c/det, a/det)
    iA = inv2(u, u.conj(), RT*u, (RT*u).conj())      # (P, Mi) = iA . (omega_1, omega_2) rows
    iB = inv2(up, up.conj(), RT*up, (RT*up).conj())
    # P = iA[0] om1 + iA[1] om2 ; Mi = iA[2] om1 + iA[3] om2 ; likewise P', Mi'
    x = K(1, 1)
    a = {}
    PA = (iA[0], iA[1]); MA = (iA[2], iA[3]); PB = (iB[0], iB[1]); MB = (iB[2], iB[3])
    for i in range(2):
        for j in range(2):
            a[(i, j)] = x*PA[i]*PB[j] + x.conj()*MA[i]*MB[j]
    w = X.add(X.scal(X.wedge(opA, opB), x), X.scal(X.wedge(omA, omB), x.conj()))
    chk = {}
    for (i, j), aij in a.items(): chk = X.add(chk, X.wedge(wA[i], wB[j]), aij)
    assert X.add(chk, w, -ONE) == {}, "a_ij do not reproduce w"
    print(f"    a_ij rational? {[ (v.b==0) for v in a.values()]}  a = {a}")
    M = K(1)
    # E' = pieces F_i x G'_j and F_i x L'^k ; ch(E') = sum_ij M a_ij/(N_i N'_j) chF_i chG_j - sum_i (M/N_i) chF_i (x) q'_i
    chEp = {}
    for (i, j), aij in a.items(): chEp = X.add(chEp, X.wedge(chF[i], chG[j]), M*aij/(N[i]*Np[j]))
    for i in range(2):
        qpi = {}
        for j in range(2): qpi = X.add(qpi, pB[j], a[(i, j)]/Np[j])
        chEp = X.add(chEp, X.wedge(chF[i], qpi), -M/N[i])
    # Lemma 2: ch(E') = M w + sum_i (M/N_i) p_i (x) (sum_j a_ij omega'_j)
    pred = X.scal(w, M)
    for i in range(2):
        Rw = {}
        for j in range(2): Rw = X.add(Rw, wB[j], a[(i, j)])
        pred = X.add(pred, X.wedge(pA[i], Rw), M/N[i])
    ok2 = X.add(chEp, pred, -ONE) == {}
    print(f"(2) ch(E') == M w + sum_i (M/N_i) p_i (x) sum_j a_ij omega'_j  (exact): {ok2}")
    assert ok2
    # (3) annihilator of ch(E') inside T D
    annEp = ann_dim(X, [th, X.wedge(opA, opB), X.wedge(omA, omB), chEp], H1T)
    print(f"(3) dim (T D cap Ann ch E') = {annEp}  [block-diagonal part = {TA+TB}] => excess over r = {TD-annEp} = 2mm' ? {TD-annEp == 2*m*mp}")
    assert TD == n*n and TA + TB == m*m + mp*mp and annEp == TA + TB
    HT2 = [(o1, o2) for i1, o1 in enumerate(H1T) for o2 in H1T[i1+1:]]   # not used (size); r is proved in the paper
    # (4) each component theta_A^k (x) R_k, k >= 1, alone is killed by no mixed direction
    for k in range(1, 2*m+1):
        Rk = {}
        for i in range(2):
            for j in range(2): Rk = X.add(Rk, wB[j], (M/N[i])*K(cA[i][k])*a[(i, j)])
        comp = X.wedge(X.power(thA, k), Rk)
        d = ann_dim(X, [th, X.wedge(opA, opB), X.wedge(omA, omB), comp], H1T)
        print(f"(4) k={k}: dim(T D cap Ann(theta_A^{k} (x) R_{k})) = {d}  [= m^2+m'^2 = {TA+TB} iff R_k != 0: {Rk != {}}]")
        assert (d == TA + TB) == (Rk != {})
    # (5) sanity: a component with R_k = 0 for k>=1 but a pure Q[theta_A] x Q[theta'] term CAN be killed
    #     by a mixed direction?  check the annihilator of theta_A^k (x) theta'^b inside T D
    for (k, b) in [(1, 0), (1, 1), (2, 1), (1, 2), (3, 0)]:
        comp = X.wedge(X.power(thA, k), X.power(thB, b))
        d = ann_dim(X, [th, X.wedge(opA, opB), X.wedge(omA, omB), comp], H1T)
        print(f"(5) theta_A^{k} (x) theta'^{b}: dim(T D cap Ann) = {d}")

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    if len(sys.argv) > 3: D = int(sys.argv[3])
    if len(sys.argv) > 1:
        run(n, m)
    else:
        run(3, 2); run(4, 2)
    print("annihilator_exact: PASS")
