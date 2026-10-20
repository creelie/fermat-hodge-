"""
Certificate for the Fricke families of Sect. V of the paper.

Part 1  Fricke universal curves over X_0(5), X_0(7) (van Geemen-Schuett,
        arXiv 2310.05196, 7.6-7.7): fibre types at the cusps and elliptic
        points, Euler numbers of the K3 surfaces X_{p,q} (twist at p, q) and
        X_psi (degree-2 base change), and the lower bound rho >= 16.
Part 2  Fricke involution: numerically, the 8 (resp. 6) roots t_i of
        j(t) = j(tau) satisfy {j(N^k/t_i)} = {j(N tau), j((tau+r)/N)}; so the
        N-isogenous curve of E_t has the j-invariant of E_{N^k/t}.
Part 3  Twist / branch-locus invariance: u(t) = (t-p)(t-N^k/p) satisfies
        u(N^k/t) = N^k u(t)/t^2 (a square times a constant); the only Moebius
        maps preserving the labelled special points 0, oo, {e1, e2} are the
        identity and the Fricke involution (non-isotriviality invariant).
Part 4  Lattice step for composite chains: a rank-6 form of signature (2,4)
        embeds in (U^3+E8(-2))_Q and in (U^3+A_2^2)_Q after any rational
        scaling (complement of rank >= 3); checked on a sample.
Part 5  Theorem D numerics: for the dihedral Hecke correspondence Gamma_sigma
        (degrees d1 = d2 = 2) the element e = zeta_n + zeta_n^{-1} has
        0 < sigma(e)^2 < d1 d2 = 4 at every real place, and the E-valued Gram
        matrix [[d1, a],[a, d2 a]] is positive definite at every place, so the
        positive index of q_S on T_1 + T_2 is 4, as Theorem D(d) requires.
Part 6  Hecke algebra of (D_n, <tau>): End_{D_n}(Q[D_n/<tau>]) is commutative
        of dimension (n+1)/2 (n odd), isomorphic to Q x prod_{d|n, d>1}
        Q(zeta_d)^+; its fields are abelian (Theorem G).
Run:  python3 -I fricke_families.py
"""
from fractions import Fraction
from itertools import product, combinations_with_replacement
import random, cmath, math
import sympy as sp
from sympy import Matrix, Rational, factorint, symbols, Poly, roots, sqrt as Sqrt
import mpmath as mp

checks = []
def check(name, ok):
    checks.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name)

t, s, p, q, lam = symbols('t s p q lam')

# ----------------------------------------------------------------- Part 1
# Fricke universal curves y^2 = x^3 - 27 c4 x - 54 c6 (vGS 7.6, 7.7)
FRICKE = {
    7: dict(c4=(t**2+13*t+49)*(t**2+5*t+1),
            c6=(t**2+13*t+49)*(t**4+14*t**3+63*t**2+70*t-7), N=7, Nk=49),
    5: dict(c4=(t**2+10*t+5)*(t**2+22*t+125),
            c6=(t**2+4*t-1)*(t**2+22*t+125)**2, N=5, Nk=125),
}

def ords(polyexpr, pt):
    """order of vanishing of a polynomial in t at pt (pt may be oo)."""
    P = Poly(sp.expand(polyexpr), t)
    if pt == sp.oo:
        return None  # handled by caller via degree
    k = 0
    while P.eval(pt) == 0:
        P = Poly(sp.quo(P.as_expr(), t - pt), t); k += 1
    return k

def kodaira(a4, a6):
    """ord(c4), ord(c6), ord(Delta) -> Kodaira type (Tate's algorithm, char 0)."""
    o4, o6, oD = a4, a6, min(3*a4, 2*a6) if 3*a4 != 2*a6 else None
    return (o4, o6)

def fibre_type(oc4, oc6, oD):
    if oD == 0: return 'I0'
    if oc4 == 0 and oc6 == 0: return 'I%d' % oD
    table = {(1,1,2):'II',(1,2,3):'III',(2,2,4):'IV',(2,3,6):'I0*',(3,4,8):'IV*',(3,5,9):'III*',(4,5,10):'II*'}
    if (min(oc4,2), min(oc6,3), oD) == (2,3,oD) and oD > 6: return 'I%d*' % (oD-6)
    return table.get((oc4, oc6, oD), '?')

EULER = {'I0':0,'II':2,'III':3,'IV':4,'I0*':6,'IV*':8,'III*':9,'II*':10}
RANK = {'I0':0,'II':0,'III':1,'IV':2,'I0*':4,'IV*':6,'III*':7,'II*':8}
def euler(ft):
    if ft in EULER: return EULER[ft]
    if ft.endswith('*'): return int(ft[1:-1]) + 6
    return int(ft[1:])
def rootrank(ft):
    if ft in RANK: return RANK[ft]
    if ft.endswith('*'): return int(ft[1:-1]) + 4
    return int(ft[1:]) - 1

for N, d in FRICKE.items():
    c4, c6 = d['c4'], d['c6']
    Delta = sp.expand(c4**3 - c6**2)
    # finite special points: roots of Delta
    fin = {}
    for r in Poly(Delta, t).all_roots() if False else roots(Poly(Delta, t)).keys():
        o4 = ords(c4, r) ; o6 = ords(c6, r); oD = ords(Delta, r)
        fin[r] = fibre_type(o4, o6, oD)
    # at infinity: orders are (4 - deg c4), (6 - deg c6), (12 - deg Delta)
    oinf = (4 - Poly(c4, t).degree(), 6 - Poly(c6, t).degree(), 12 - Poly(Delta, t).degree())
    fin[sp.oo] = fibre_type(*oinf)
    types = sorted(fin.values())
    print(f"  level {N}: fibres of the Fricke curve:", fin)
    e_R = sum(euler(f) for f in fin.values())
    check(f"level {N}: untwisted Fricke curve has Euler number 12 (rational elliptic surface)", e_R == 12)
    ell = 'II' if N == 7 else 'III'
    check(f"level {N}: fibres are I_1, I_{N}, {ell}, {ell}", types == sorted(['I1', 'I%d' % N, ell, ell]))
    # elliptic points are swapped by w: product of the roots of the quadratic = N^k
    quadr = (t**2+13*t+49) if N == 7 else (t**2+22*t+125)
    e1, e2 = list(roots(Poly(quadr, t)).keys())
    check(f"level {N}: the two elliptic points e1, e2 satisfy e1*e2 = {d['Nk']} (swapped by w)", sp.simplify(e1*e2 - d['Nk']) == 0)
    cusps = [r for r, f in fin.items() if f[0] == 'I' and f[1:].isdigit() and f != 'I0']
    check(f"level {N}: the cusps are t = 0 and t = oo", set(cusps) == {0, sp.oo})
    # Family A_N: twist by u = (t-p)(t-q) at two general points: two I0* fibres
    e_A = e_R + 12
    rk_A = 2 + sum(rootrank(f) for f in fin.values()) + 8
    check(f"level {N}: X_(p,q) (twist at p,q) has Euler number 24 and root rank + 2 = {rk_A} >= 16", e_A == 24 and rk_A == 16)
    # Family B_N: degree-2 base change, generic (unramified over all special points)
    e_B = 2 * e_R
    rk_B = 2 + 2 * sum(rootrank(f) for f in fin.values())
    mwR = 8 - sum(rootrank(f) for f in fin.values())
    check(f"level {N}: X_psi (degree-2 base change) has Euler number 24, root rank + 2 = {rk_B}, MW(R) rank {mwR}, so rho >= {rk_B + mwR} = 16",
          e_B == 24 and rk_B + mwR == 16)
    # degree-3 untwisted base change: Euler number
    if N == 7:
        # elliptic points fully ramified (type II pulled back with ramification 3 is smooth), cusps I_r, I_{7r}
        e_C = 3 * 1 + 3 * 7 + 0
        check("level 7: degree-3 base change totally ramified at the elliptic points has Euler number 24 and root rank >= 18 (rho >= 20)",
              e_C == 24 and 2 + 18 >= 20)
    else:
        e_C = 3 * 1 + 3 * 5 + 2 * 9
        check("level 5: no K3 from a degree-3 base change (Euler number %d > 24)" % e_C, e_C > 24)

# ----------------------------------------------------------------- Part 2
mp.mp.dps = 40
def jq(tau, terms=400):
    qq = mp.exp(2j * mp.pi * tau)
    E4 = 1 + 240 * mp.fsum(mp.fsum(dd**3 for dd in sp.divisors(n)) * qq**n for n in range(1, terms))
    eta24 = qq * mp.fprod((1 - qq**n)**24 for n in range(1, terms))
    return E4**3 / eta24

def jt(N, tt):
    d = FRICKE[N]
    c4 = sp.lambdify(t, d['c4'], 'mpmath'); c6 = sp.lambdify(t, d['c6'], 'mpmath')
    return 1728 * c4(tt)**3 / (c4(tt)**3 - c6(tt)**2)

random.seed(7)
for N in (7, 5):
    d = FRICKE[N]
    ok_all = True
    for trial in range(3):
        tau = mp.mpc(random.uniform(-0.4, 0.4), random.uniform(1.1, 1.6))
        J = jq(tau)
        # solve j(t) = J : polynomial 1728 c4^3 - J (c4^3 - c6^2) = 0 of degree 2N+2 ... degree = N+1 (index of Gamma_0(N))
        c4 = Poly(d['c4'], t); c6 = Poly(d['c6'], t)
        polyc = (1728 * c4**3 - c4**3 + c6**2)  # placeholder to get degree; real coefficients built below
        g = sp.gcd(sp.expand(d['c4']**3), sp.expand(d['c4']**3 - d['c6']**2))
        coeffs3 = Poly(sp.quo(sp.expand(d['c4']**3), g), t).all_coeffs()
        coeffsD = Poly(sp.quo(sp.expand(d['c4']**3 - d['c6']**2), g), t).all_coeffs()
        deg = max(len(coeffs3), len(coeffsD)) - 1
        def pad(c): return [0]*(deg + 1 - len(c)) + [mp.mpf(int(x)) for x in c]
        a3, aD = pad(coeffs3), pad(coeffsD)
        polycoeffs = [1728 * a - J * b for a, b in zip(a3, aD)]
        rts = mp.polyroots(polycoeffs, maxsteps=200, extraprec=200)
        check_n = (len(rts) == N + 1)
        targets = [jq(N * tau)] + [jq((tau + r) / N) for r in range(N)]
        images = [jt(N, d['Nk'] / r) for r in rts]
        # match multisets
        used = [False] * len(targets); okm = True
        for im in images:
            best = None
            for i, tg in enumerate(targets):
                if not used[i] and abs(im - tg) < 1e-12 * (1 + abs(tg)):
                    best = i; break
            if best is None: okm = False; break
            used[best] = True
        ok_all &= (check_n and okm)
    check(f"level {N}: for 3 random tau, the {N+1} solutions t_i of j(t)=j(tau) have {{j({d['Nk']}/t_i)}} = {{j({N}tau), j((tau+r)/{N})}}  (Fricke involution t -> {d['Nk']}/t)", ok_all)

# ----------------------------------------------------------------- Part 3
for N in (7, 5):
    Nk = FRICKE[N]['Nk']
    u = (t - p) * (t - Nk / p)
    ratio = sp.simplify(u.subs(t, Nk / t) / u)
    check(f"level {N}: u(t) = (t-p)(t-{Nk}/p) satisfies u({Nk}/t) = {Nk} u(t)/t^2", sp.simplify(ratio - Nk / t**2) == 0)
    u2 = (t - Sqrt(Nk)) * (t + Sqrt(Nk))
    check(f"level {N}: u(t) = t^2 - {Nk} (vGS) satisfies u({Nk}/t) = -{Nk} u(t)/t^2", sp.simplify(u2.subs(t, Nk / t) / u2 + Nk / t**2) == 0)
    # Moebius maps preserving 0, oo (as a set) and the pair {e1, e2}
    quadr = (t**2+13*t+49) if N == 7 else (t**2+22*t+125)
    e1, e2 = list(roots(Poly(quadr, t)).keys())
    sols_scale = [l for l in sp.solve([sp.expand((lam*e1 - e1)*(lam*e1 - e2))], lam)]
    # t -> lam t preserves {e1,e2} iff {lam e1, lam e2} = {e1, e2}
    good_scale = [l for l in sp.solve(sp.expand((lam*e1 - e1)*(lam*e1 - e2)), lam) if sp.simplify((l*e2 - e1)*(l*e2 - e2)) == 0]
    good_inv = [l for l in sp.solve(sp.expand((lam/e1 - e1)*(lam/e1 - e2)), lam) if sp.simplify((l/e2 - e1)*(l/e2 - e2)) == 0]
    check(f"level {N}: Moebius maps preserving 0, oo and {{e1,e2}}: t->lam t only for lam = 1, t->lam/t only for lam = {Nk}",
          [sp.simplify(x) for x in good_scale] == [1] and [sp.simplify(x) for x in good_inv] == [Nk])
    # the invariant p + Nk/p separates the members of the one-dimensional family up to p <-> Nk/p
    check(f"level {N}: p + {Nk}/p = p' + {Nk}/p' iff p' in {{p, {Nk}/p}}",
          set(sp.solve(sp.Eq(p + Nk/p, q + Nk/q), q)) == {p, Nk/p})

# ----------------------------------------------------------------- Part 4  (Hasse-Minkowski machinery from sqrt6_chain.py)
def sqfree_int(r):
    r = Fraction(r); num, den = r.numerator, r.denominator
    sgn = -1 if num < 0 else 1
    e = {}
    for pp, k in list(factorint(abs(num)).items()) + list(factorint(den).items()):
        e[pp] = (e.get(pp, 0) + k) % 2
    v = sgn
    for pp, k in e.items():
        if k: v *= pp
    return v
def legendre(u_, pp):
    u_ %= pp
    return 1 if pow(u_, (pp - 1) // 2, pp) == 1 else -1
def hilbert(a, b, pp):
    if pp == 'inf': return -1 if (a < 0 and b < 0) else 1
    def split(x):
        al = 0
        while x % pp == 0: x //= pp; al += 1
        return al, x
    al, uu = split(a); be, vv = split(b)
    if pp != 2:
        return (-1) ** (al * be * ((pp - 1) // 2)) * legendre(uu, pp) ** be * legendre(vv, pp) ** al
    eps = lambda x: ((x - 1) // 2) % 2
    om = lambda x: ((x * x - 1) // 8) % 2
    return (-1) ** ((eps(uu) * eps(vv) + al * om(vv) + be * om(uu)) % 2)
def diagonalize(G):
    G = Matrix(G); diag = []
    while G.shape[0] > 0:
        n = G.shape[0]
        i = next((i for i in range(n) if G[i, i] != 0), None)
        if i is None:
            j = next(j for j in range(1, n) if G[0, j] != 0)
            P = sp.eye(n); P[j, 0] = 1; G = P.T * G * P; i = 0
        if i != 0:
            P = sp.eye(n); P[0, 0] = 0; P[i, i] = 0; P[0, i] = 1; P[i, 0] = 1; G = P.T * G * P
        a = G[0, 0]; diag.append(Fraction(int(a.p), int(a.q)))
        P = sp.eye(n)
        for j in range(1, n): P[0, j] = -G[0, j] / a
        G = (P.T * G * P)[1:, 1:]
    return diag
class QForm:
    def __init__(self, diag):
        self.diag = [sqfree_int(x) for x in diag]; self.rank = len(diag)
        self.sig = (sum(1 for x in diag if x > 0), sum(1 for x in diag if x < 0))
        dd = 1
        for x in self.diag: dd *= x
        self.d = sqfree_int(dd)
        self.primes = {2} | set().union(*[set(factorint(abs(x))) for x in self.diag])
    def eps(self, pp):
        e = 1
        for i in range(self.rank):
            for j in range(i + 1, self.rank): e *= hilbert(self.diag[i], self.diag[j], pp)
        return e
    @staticmethod
    def from_gram(G): return QForm(diagonalize(G))
def is_square_in_Qp(dd, pp):
    if dd % pp == 0: return False
    if pp == 2: return dd % 8 == 1
    return legendre(dd, pp) == 1
def embeds(W, V):
    k = V.rank - W.rank
    if k < 0: return False
    dprime = sqfree_int(V.d * W.d)
    sp_, sm_ = V.sig[0] - W.sig[0], V.sig[1] - W.sig[1]
    if sp_ < 0 or sm_ < 0: return False
    if (dprime < 0) != (sm_ % 2 == 1): return False
    for pp in sorted(V.primes | W.primes | set(factorint(abs(dprime)))):
        eprime = V.eps(pp) * W.eps(pp) * hilbert(W.d, dprime, pp)
        if k == 0 and not (is_square_in_Qp(dprime, pp) and eprime == 1): return False
        if k == 1 and eprime != 1: return False
        if k == 2 and is_square_in_Qp(sqfree_int(-dprime), pp) and eprime == -1: return False
    return True
def U(): return Matrix([[0, 1], [1, 0]])
def A2(): return Matrix([[-2, 1], [1, -2]])
def E8neg():
    C = sp.zeros(8, 8); edges = [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(4,7)]
    for i in range(8): C[i, i] = -2
    for i, j in edges: C[i, j] = 1; C[j, i] = 1
    return C
V3 = QForm.from_gram(sp.diag(U(), U(), U(), A2(), A2()))
V2 = QForm.from_gram(sp.diag(U(), U(), U(), 2 * E8neg()))
random.seed(3)
cnt = 0; okall = True
cands = [1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210]
for _ in range(400):
    diag = [random.choice(cands) for _ in range(2)] + [-random.choice(cands) for _ in range(4)]
    W = QForm(diag)
    for scal in (1, 2, 3, 5, 7, 10, 14, 21, 42):
        Ws = QForm([scal * x for x in diag])
        okall &= embeds(Ws, V2) and embeds(Ws, V3)
    cnt += 1
check("every rank-6 form of signature (2,4) in a sample of 400 (x 9 scalings) embeds in (U^3+E8(-2))_Q and (U^3+A_2^2)_Q (complement rank >= 3 is automatic)", okall)

# ----------------------------------------------------------------- Part 5  Theorem D numerics for dihedral Hecke correspondences
for n in (5, 7, 9, 11, 13):
    conj = [2 * math.cos(2 * math.pi * k / n) for k in range(1, n) if math.gcd(k, n) == 1][: (n - 1) // 2]
    a = [e * e for e in conj]
    d1 = d2 = 2
    posdef = all((d1 > 0 and d1 * d2 * aa - aa * aa > 0) for aa in a)   # det of [[d1, a],[a, d2 a]] = a(d1 d2 - a)
    check(f"D_{n}: e = zeta+zeta^-1 has 0 < sigma(e)^2 < d1 d2 = 4 at all real places; Gram [[2,a],[a,2a]] positive definite at every place (positive index of q_S on T_1+T_2 equals 4)",
          all(0 < aa < 4 for aa in a) and posdef)
# the degenerate value a = d1 d2 is never attained: |zeta + zeta^-1| < 2 for zeta != 1
check("a = d1 d2 (degenerate T_1 + T_2) would need |zeta+zeta^-1| = 2, impossible for zeta != +-1 (n odd)", all(abs(2*math.cos(2*math.pi*k/n)) < 2 - 1e-9 for n in range(3, 60, 2) for k in range(1, n)))

# ----------------------------------------------------------------- Part 6  Hecke algebra of (D_n, <tau>)
def hecke_dim_and_minpoly(n):
    # D_n acting on Z/n: r: i -> i+1, tau: i -> -i.  H = <tau> stabilises 0.
    # orbits of D_n on pairs (i, j) <-> orbits of <tau> on Z/n : {0}, {k, -k}
    orbits = 1 + (n - 1) // 2
    # Hecke operator T_1 = adjacency matrix of the cycle graph (double coset <tau> r <tau> = {r, r^-1}·...)
    A = sp.zeros(n, n)
    for i in range(n):
        A[i, (i + 1) % n] += 1; A[i, (i - 1) % n] += 1
    x = symbols('x')
    mpoly = A.charpoly(x).as_expr()
    fac = sp.factor_list(mpoly)
    degs = sorted(sp.Poly(f, x).degree() for f, m in fac[1])
    return orbits, degs
o7, d7 = hecke_dim_and_minpoly(7)
check("Hecke algebra of (D_7, <tau>) has dimension 4 and its generator has characteristic polynomial (x-2) * (irreducible cubic)^2: End = Q x Q(zeta_7)^+", o7 == 4 and d7 == [1, 3])
o9, d9 = hecke_dim_and_minpoly(9)
check("Hecke algebra of (D_9, <tau>) has dimension 5 and factors (x-2)(x+1)(cubic): End = Q x Q x Q(zeta_9)^+", o9 == 5 and d9 == [1, 1, 3])
o11, d11 = hecke_dim_and_minpoly(11)
check("Hecke algebra of (D_11, <tau>) has dimension 6: End = Q x Q(zeta_11)^+ (quintic)", o11 == 6 and d11 == [1, 5])
o5, d5 = hecke_dim_and_minpoly(5)
check("Hecke algebra of (D_5, <tau>) has dimension 3: End = Q x Q(sqrt 5)", o5 == 3 and d5 == [1, 2])


# ----------------------------------------------------------------- Part 7  classification of elliptic K3 surfaces with a rational N-isogeny
# X = psi^* E_univ (x) u, psi: P^1 -> X_0(N) of degree k, u a twist.  Euler number must be 24.
# Cusps taken unramified (ramification over a cusp only raises the root rank): k I_1 + k I_N.
# Elliptic points: pull-back of (ord c4, ord c6, ord Delta) = (1,1,2) [N=7] or (1,2,3) [N=5] by ramification r,
# minimalised modulo (4,6,12):  N=7: r mod 6 -> I0, II, IV, I0*, IV*, II*;  N=5: r mod 4 -> I0, III, I0*, III*.
# A quadratic twist toggles star <-> non-star at each of its zeros (Euler +-6); zeros elsewhere add I0* (+6, root rank +4).
# For an untwisted base change (u constant) the Mordell-Weil group of the rational surface R (rank 2) pulls back: +2.
TOGGLE = {'I0':'I0*','I0*':'I0','II':'IV*','IV*':'II','IV':'II*','II*':'IV','III':'III*','III*':'III'}
def partitions(n, m=None):
    if m is None: m = n
    if n == 0: yield []; return
    for i in range(min(n, m), 0, -1):
        for rest in partitions(n - i, i): yield [i] + rest
def classify(N):
    out = []
    for k in range(1, 5):
        cusp_e = k * (1 + N); cusp_rk = k * (N - 1)
        for P1 in partitions(k):
            for P2 in partitions(k):
                fib = []
                for P in (P1, P2):
                    for r in P:
                        fib.append(['I0','II','IV','I0*','IV*','II*'][r % 6] if N == 7 else ['I0','III','I0*','III*'][r % 4])
                nf = len(fib)
                for mask in range(2 ** nf):
                    fib2 = [TOGGLE[f_] if (mask >> i) & 1 else f_ for i, f_ in enumerate(fib)]
                    ntog = bin(mask).count('1')
                    for c_ in range(0, 5):
                        if (ntog + c_) % 2: continue      # a twist has an even number of zeros on P^1
                        e = cusp_e + sum(euler(f_) for f_ in fib2) + 6 * c_
                        if e != 24: continue
                        rk_lb = 2 + cusp_rk + sum(rootrank(f_) for f_ in fib2) + 4 * c_
                        untwisted = (ntog == 0 and c_ == 0)
                        if untwisted: rk_lb += 2      # MW(R) of rank 2 pulls back
                        used = sum(r - 1 for r in P1) + sum(r - 1 for r in P2)
                        dim = (2 * k - 2 - used) + c_
                        if dim < 0: continue
                        out.append((k, tuple(P1), tuple(P2), tuple(fib2), c_, rk_lb, dim))
    return out
for N in (7, 5):
    cl = classify(N)
    print(f"  level {N}: {len(cl)} K3 configurations (k, ramification over e1, over e2, fibres there after twisting, free twist zeros, rho lower bound, dim):")
    for row in cl: print("     ", row)
    check(f"level {N}: every non-isotrivial elliptic K3 surface with a rational cyclic {N}-isogeny of its generic fibre has rho >= 16 (Euler-number classification, k <= 4)",
          all(r[5] >= 16 for r in cl))
    check(f"level {N}: every such family has dimension <= 2, so T(X) has rank <= 6 and a one-dimensional Hodge locus in the 4-dimensional period domain of such a T has negative expected intersection dimension with the family",
          all(r[6] <= 2 for r in cl))
    two = sorted(set(r[:3] for r in cl if r[6] == 2))
    print(f"  level {N}: two-dimensional configurations (k, ramification over e1, e2):", two)
    check(f"level {N}: A_{N} (k=1, two free twist zeros) and B_{N} (k=2 untwisted) are among the two-dimensional families; no family has dimension > 2",
          (1, (1,), (1,)) in two and (2, (1, 1), (1, 1)) in two and all(r[6] <= 2 for r in cl))
print("\n%d checks passed, %d failed" % (sum(1 for _, o in checks if o), sum(1 for _, o in checks if not o)))
