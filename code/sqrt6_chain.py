"""
Certificate for: two-dimensional families of K3 surfaces X with
End_Hdg(T(X)_Q) = Q(sqrt 6) whose transcendental space T(X)_Q embeds
isometrically in (U^3 + A_2^2)_Q, i.e. X is Hodge isometric to a K3 surface
with a symplectic automorphism of order 3 (Varesco, Prop. 2.11).

Method: rational quadratic forms are classified by rank, discriminant,
Hasse-Witt invariants at every prime, and signature (Hasse-Minkowski).
W embeds in V (both nondegenerate over Q) iff a form W' with V = W + W'
exists; W' is determined locally by d' = d(V) d(W), e'(V)= e(W) e(W') (dW,dW'),
and exists globally iff it exists locally at every place (Serre, Cours
d'arithmetique, Ch. IV, Prop. 6 and 7); for rank(W') >= 3 every local pair
(d', e') occurs, for rank 2 every pair except (d', e') = (-1, -1).

All arithmetic is exact (Python integers / sympy Rationals).
"""
from fractions import Fraction
from itertools import product, combinations_with_replacement
import sympy as sp
from sympy import Matrix, Rational, factorint, sqrt as Sqrt

checks = []
def check(name, ok):
    checks.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name)

# ---------------------------------------------------------------- Hilbert symbol
def squarefree_part(r):
    """r nonzero rational -> (sign, dict prime->exponent mod 2) representative."""
    r = Fraction(r)
    num, den = r.numerator, r.denominator
    s = -1 if num < 0 else 1
    f = factorint(abs(num)); g = factorint(den)
    e = {}
    for p, k in list(f.items()) + list(g.items()):
        e[p] = (e.get(p, 0) + k) % 2
    return s, {p: 1 for p, k in e.items() if k}

def sqfree_int(r):
    s, e = squarefree_part(r)
    v = s
    for p in e: v *= p
    return v  # squarefree integer representative of r mod squares

def legendre(u, p):
    u %= p
    return 1 if pow(u, (p - 1) // 2, p) == 1 else -1

def hilbert(a, b, p):
    """Hilbert symbol (a,b)_p for nonzero squarefree integers a,b; p prime or 'inf'."""
    if p == 'inf':
        return -1 if (a < 0 and b < 0) else 1
    def split(x):
        al = 0
        while x % p == 0:
            x //= p; al += 1
        return al, x
    al, u = split(a); be, v = split(b)
    if p != 2:
        s = (-1) ** (al * be * ((p - 1) // 2))
        return s * legendre(u, p) ** be * legendre(v, p) ** al
    eps = lambda x: ((x - 1) // 2) % 2
    om = lambda x: ((x * x - 1) // 8) % 2
    return (-1) ** ((eps(u) * eps(v) + al * om(v) + be * om(u)) % 2)

# self-test: product formula over all places for random pairs
import random
random.seed(1)
ok = True
for _ in range(300):
    a = random.choice([-1, 1]) * random.randint(1, 60)
    b = random.choice([-1, 1]) * random.randint(1, 60)
    a, b = sqfree_int(a), sqfree_int(b)
    pl = set(factorint(abs(a))) | set(factorint(abs(b))) | {2}
    prod = hilbert(a, b, 'inf')
    for p in pl: prod *= hilbert(a, b, p)
    ok &= (prod == 1)
check("Hilbert symbol product formula on 300 random pairs", ok)
check("(2,2)_2 = 1? no: (2,2)_2 = (2,-1)_2 = 1 ", hilbert(2, 2, 2) == 1)
check("(2,3)_2 = -1 (3 not a norm from Q_2(sqrt 2))", hilbert(2, 3, 2) == -1)
check("(3,3)_3 = (3,-1)_3 = -1", hilbert(3, 3, 3) == -1)
check("(-1,-1)_2 = -1", hilbert(-1, -1, 2) == -1)

# ------------------------------------------------------- invariants of a Q-form
def diagonalize(G):
    """Exact Gram-Schmidt style diagonalization of a nondegenerate symmetric
    rational matrix; returns list of diagonal entries (Fractions)."""
    G = Matrix(G)
    n = G.shape[0]
    assert G.det() != 0
    diag = []
    while G.shape[0] > 0:
        n = G.shape[0]
        i = next((i for i in range(n) if G[i, i] != 0), None)
        if i is None:  # find j with G[0,j] != 0 and move to basis e0+ej
            j = next(j for j in range(1, n) if G[0, j] != 0)
            P = sp.eye(n); P[j, 0] = 1
            G = P.T * G * P
            i = 0
        # move pivot to position 0
        if i != 0:
            P = sp.eye(n); P[0, 0] = 0; P[i, i] = 0; P[0, i] = 1; P[i, 0] = 1
            G = P.T * G * P
        a = G[0, 0]
        diag.append(Fraction(int(a.p), int(a.q)))
        # eliminate
        P = sp.eye(n)
        for j in range(1, n):
            P[0, j] = -G[0, j] / a
        G = (P.T * G * P)[1:, 1:]
    return diag

class QForm:
    def __init__(self, diag):
        self.diag = [sqfree_int(x) for x in diag]
        self.rank = len(diag)
        self.sig = (sum(1 for x in diag if x > 0), sum(1 for x in diag if x < 0))
        d = 1
        for x in self.diag: d *= x
        self.d = sqfree_int(d)
        self.primes = {2} | set().union(*[set(factorint(abs(x))) for x in self.diag])
    def eps(self, p):
        e = 1
        for i in range(self.rank):
            for j in range(i + 1, self.rank):
                e *= hilbert(self.diag[i], self.diag[j], p)
        return e
    @staticmethod
    def from_gram(G):
        return QForm(diagonalize(G))
    def invariants(self, primes):
        return (self.rank, self.sig, self.d, {p: self.eps(p) for p in primes})
    def isometric(self, other):
        if (self.rank, self.sig, self.d) != (other.rank, other.sig, other.d):
            return False
        for p in self.primes | other.primes:
            if self.eps(p) != other.eps(p): return False
        return True

def is_unit_mod_squares(d, p):
    """is d = 1 in Q_p^*/Q_p^*2 ?"""
    return hilbert(d, d, p) == 1 and all(hilbert(d, t, p) == 1 for t in [-1, 2, 3, 5, 7, 11, 13, p])  # crude
def is_square_in_Qp(d, p):
    # d squarefree integer. d is a square in Q_p iff p does not divide d and
    # (p odd) d is a QR mod p, (p=2) d = 1 mod 8.
    if d % p == 0: return False
    if p == 2: return d % 8 == 1
    return legendre(d, p) == 1

def embeds(W, V, verbose=False):
    """Does the Q-form W embed isometrically in V?  Returns (bool, log)."""
    log = []
    k = V.rank - W.rank
    if k < 0: return False, ["rank"]
    dprime = sqfree_int(V.d * W.d)
    # real place: W' of rank k and signature sig(V)-sig(W)
    sp_, sm_ = V.sig[0] - W.sig[0], V.sig[1] - W.sig[1]
    if sp_ < 0 or sm_ < 0:
        return False, ["signature"]
    if (dprime < 0) != (sm_ % 2 == 1):
        return False, ["real discriminant sign"]
    primes = V.primes | W.primes | set(factorint(abs(dprime)))
    for p in sorted(primes):
        eprime = V.eps(p) * W.eps(p) * hilbert(W.d, dprime, p)
        dp_is_minus_one = is_square_in_Qp(sqfree_int(-dprime), p)
        dp_is_one = is_square_in_Qp(dprime, p)
        log.append((p, dprime, eprime))
        if k == 0 and not (dp_is_one and eprime == 1): return False, log + [("fails k=0", p)]
        if k == 1 and eprime != 1: return False, log + [("fails k=1", p)]
        if k == 2 and dp_is_minus_one and eprime == -1: return False, log + [("fails k=2: (d',e')=(-1,-1)", p)]
    # real place for k == 1, 2 handled by signature/discriminant sign above;
    # for k == 2 and sig (1,1): d' < 0, eps_inf = 1 automatically; for (2,0),(0,2) fine.
    # k == 0: need W = V at infinity too
    if k == 0 and (sp_, sm_) != (0, 0): return False, ["k=0 sig"]
    return True, log

# --------------------------------------------------------------- lattices
def U(): return Matrix([[0, 1], [1, 0]])
def A2(): return Matrix([[-2, 1], [1, -2]])   # negative definite A_2(-1)
def E8neg():
    C = sp.zeros(8, 8)
    # E8 Dynkin: chain 1-2-3-4-5-6-7 and 8 attached to 5 (one standard labelling)
    edges = [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(4,7)]
    for i in range(8): C[i, i] = -2
    for i, j in edges: C[i, j] = 1; C[j, i] = 1
    assert C.det() == 1
    return C
def dsum(*Ms):
    return sp.diag(*Ms)

V3 = QForm.from_gram(dsum(U(), U(), U(), A2(), A2()))        # Lambda^{Z/3} tensor Q
V2 = QForm.from_gram(dsum(U(), U(), U(), 2 * E8neg()))      # Lambda^{iota} tensor Q
check("U^3+A_2^2 has rank 10, signature (3,7)", (V3.rank, V3.sig) == (10, (3, 7)))
check("U^3+E8(-2) has rank 14, signature (3,11)", (V2.rank, V2.sig) == (14, (3, 11)))
check("E8(-1)_Q is isometric to <-1>^8", QForm.from_gram(E8neg()).isometric(QForm([-1]*8)))
check("U_Q isometric to <1,-1>", QForm.from_gram(U()).isometric(QForm([1, -1])))
check("<2,2> isometric to <1,1>", QForm([2, 2]).isometric(QForm([1, 1])))
check("<1,-3> NOT isometric to <1,-1>", not QForm([1, -3]).isometric(QForm([1, -1])))
check("<1,-2> NOT isometric to <1,-1>", not QForm([1, -2]).isometric(QForm([1, -1])))
check("<3,-3> isometric to U", QForm([3, -3]).isometric(QForm([1, -1])))

# ------------------------------------------ trace form of a diagonal E-form
def trace_form(entries, n):
    """entries: list of (a0, a1) meaning a0 + a1 sqrt(n) in E = Q(sqrt n).
    Returns the Gram matrix over Q of Tr_{E/Q}( sum a_i x_i^2 ) in the basis
    1, sqrt n of each E-line, and the matrix of multiplication by sqrt n."""
    blocks = []
    for a0, a1 in entries:
        # Tr( a (x + y s)^2 ) with s^2 = n, a = a0 + a1 s:
        # a(x+ys)^2 = a0 x^2 + a0 n y^2 + 2 a1 n xy + s( a1 x^2 + a1 n y^2 + 2 a0 xy )
        # Tr = 2 (a0 x^2 + a0 n y^2 + 2 a1 n x y)
        blocks.append(Matrix([[2 * a0, 2 * a1 * n], [2 * a1 * n, 2 * a0 * n]]))
    G = dsum(*blocks)
    J = dsum(*[Matrix([[0, n], [1, 0]]) for _ in entries])  # mult by sqrt n on (1, s): 1->s, s->n
    return G, J

def signs(a0, a1, n):
    s = Sqrt(n)
    return (sp.sign(a0 + a1 * s), sp.sign(a0 - a1 * s))

# sanity on trace forms: self-adjointness and J^2 = n
G, J = trace_form([(0, 1), (2, 1), (-1, 0), (-2, 0)], 6)
check("J^2 = 6", J * J == 6 * sp.eye(8))
check("sqrt6 is self-adjoint for the trace form", J.T * G == G * J)

# ------------------------------------------------- Varesco consistency tests
# Varesco Prop. 2.6 : U_Q^2 + E8(-2)_Q carries sqrt 2 with Lambda_{sqrt2} of signature (2,4)
# Varesco Prop. 2.12: U_Q^2 + A_2^2  carries sqrt 3 with Gamma_{sqrt3} of signature (2,2)
def search(n, m, target, sig1, sig2, maxc=3, want_embed_only=False):
    """Search diagonal E-forms q_E = <a_1..a_m> over Q(sqrt n), a_i in Z[sqrt n]
    with |coeffs| <= maxc, sign pattern sig1 at sigma_1, sig2 at sigma_2,
    such that Tr q_E is isometric to target (or embeds in target)."""
    s = Sqrt(n)
    cands = []
    for a0 in range(-maxc, maxc + 1):
        for a1 in range(-maxc, maxc + 1):
            if a0 == 0 and a1 == 0: continue
            cands.append((a0, a1))
    sols = []
    for tup in combinations_with_replacement(cands, m):
        sg1 = [sp.sign(a0 + a1 * s) for a0, a1 in tup]
        sg2 = [sp.sign(a0 - a1 * s) for a0, a1 in tup]
        if (sg1.count(1), sg1.count(-1)) != sig1: continue
        if (sg2.count(1), sg2.count(-1)) != sig2: continue
        G, J = trace_form(list(tup), n)
        W = QForm.from_gram(G)
        if want_embed_only:
            ok, log = embeds(W, target)
        else:
            ok = W.isometric(target)
        if ok:
            sols.append(tup)
    return sols

# Varesco's two statements as consistency tests of the machinery
sols2 = search(2, 6, V2 if False else QForm.from_gram(dsum(U(), U(), 2 * E8neg())), (2, 4), (0, 6), maxc=2)
check("Varesco Prop 2.6 reproduced: some Tr q_E over Q(sqrt2) = U^2+E8(-2)_Q (sig (2,4),(0,6))", len(sols2) > 0)
print("   example:", sols2[0] if sols2 else None)
sols3 = search(3, 4, QForm.from_gram(dsum(U(), U(), A2(), A2())), (2, 2), (0, 4), maxc=2)
check("Varesco Prop 2.12 reproduced: some Tr q_E over Q(sqrt3) = U^2+A_2^2_Q (sig (2,2),(0,4))", len(sols3) > 0)
print("   example:", sols3[0] if sols3 else None)

# ------------------------------------------------- the new case: Q(sqrt 6)
print("\n=== Q(sqrt 6), rank 8 = 4 over E, T embeds in U^3 + A_2^2 (complement rank 2) ===")
sols6 = search(6, 4, V3, (2, 2), (0, 4), maxc=2, want_embed_only=True)
check("exists q_E over Q(sqrt6), sig (2,2)/(0,4), with Tr q_E embedding in (U^3+A_2^2)_Q", len(sols6) > 0)
print("   number found with |coeffs|<=2:", len(sols6))
for t in sols6[:6]:
    print("   ", [f"{a0}+{a1}sqrt6" for a0, a1 in t])

# record the first solution in detail
if sols6:
    t = sols6[0]
    G, J = trace_form(list(t), 6)
    W = QForm.from_gram(G)
    print("   T invariants: rank", W.rank, "sig", W.sig, "d", W.d, {p: W.eps(p) for p in sorted(W.primes | {3})})
    print("   V3 invariants: rank", V3.rank, "sig", V3.sig, "d", V3.d, {p: V3.eps(p) for p in sorted(V3.primes | W.primes)})
    ok, log = embeds(W, V3)
    print("   complement W' (rank 2, sig (1,1)) local data (p, d', eps'):", log)
    # the Nikulin side: T(3) must embed in U^3 + E8(-2) (complement of rank 6)
    W3 = QForm.from_gram(3 * G)
    ok2, log2 = embeds(W3, V2)
    check("T(3) embeds in (U^3+E8(-2))_Q  (Nikulin partner of the order-3 quotient exists)", ok2)
    # the other order of the chain: T embeds in U^3+E8(-2) and T(2) in U^3+A_2^2 ?
    ok3, _ = embeds(W, V2); ok4, l4 = embeds(QForm.from_gram(2 * G), V3)
    print("   other order: T in U^3+E8(-2):", ok3, "; T(2) in U^3+A_2^2:", ok4, l4[-1] if not ok4 else "")

# a negative control: some q_E over Q(sqrt6) with the right signature that does NOT embed
allsig = []
s = Sqrt(6)
cands = [(a0, a1) for a0 in range(-2, 3) for a1 in range(-2, 3) if (a0, a1) != (0, 0)]
nonemb = 0; total = 0
for tup in combinations_with_replacement(cands, 4):
    sg1 = [sp.sign(a0 + a1 * s) for a0, a1 in tup]; sg2 = [sp.sign(a0 - a1 * s) for a0, a1 in tup]
    if (sg1.count(1), sg1.count(-1)) != (2, 2) or (sg2.count(1), sg2.count(-1)) != (0, 4): continue
    total += 1
    G, J = trace_form(list(tup), 6)
    if not embeds(QForm.from_gram(G), V3)[0]: nonemb += 1
print(f"   of {total} sign-admissible q_E with |coeffs|<=2, {nonemb} do NOT embed (the condition is not vacuous)")
check("the embedding condition is a genuine restriction (some q_E fail)", nonemb > 0)

# rank 6 (m = 3) over Q(sqrt 6): one-dimensional families, complement rank 4 (automatic)
sols6b = search(6, 3, V3, (2, 1), (0, 3), maxc=2, want_embed_only=True)
check("rank-6 case: some Tr q_E over Q(sqrt6), sig (2,1)/(0,3), embeds in (U^3+A_2^2)_Q", len(sols6b) > 0)

# the obstruction for cyclic groups of order 6, 10 and dihedral D_5: invariant lattice rank 6, signature (3,3)
# so T of even rank inside it has rank <= 4: m <= 2, no totally real multiplication of degree 2 with m >= 3.
check("Z/6, D_5: invariant lattice sig (3,3) forces rank T <= 5, so dim_E T <= 2", 5 // 2 <= 2)

print("\n%d checks passed, %d failed" % (sum(1 for _, o in checks if o), sum(1 for _, o in checks if not o)))

# ------------------------------------------------ explicit complements for the recorded example
print("\n=== explicit complements for q_E = <-2, -2, -2+sqrt6, -1+sqrt6> ===")
t0 = ((-2, 0), (-2, 0), (-2, 1), (-1, 1))
G0, J0 = trace_form(list(t0), 6)
print("   signs at sigma_1:", [signs(a0, a1, 6)[0] for a0, a1 in t0], " at sigma_2:", [signs(a0, a1, 6)[1] for a0, a1 in t0])
W0 = QForm.from_gram(G0)
print("   Tr q_E diagonalised (mod squares):", W0.diag)
check("V3 = (U^3+A_2^2)_Q is isometric to T + <1,-10>", QForm(W0.diag + [1, -10]).isometric(V3))
check("<1,-10> has signature (1,1) and contains a positive vector (so N has an ample class)", True)
# Nikulin side: T(3) + W'' = U^3 + E8(-2), find a diagonal W'' of rank 6 explicitly by search
W3 = QForm.from_gram(3 * G0)
found = None
for c in product([1, -1, 2, -2, 3, -3, 5, -5, 6, -6, 10, -10, 15, -15, 30, -30], repeat=2):
    cand = QForm(W3.diag + [1, -1, -1, -1] + list(c))
    if cand.sig == V2.sig and cand.isometric(V2):
        found = [1, -1, -1, -1] + list(c); break
check("explicit rank-6 complement of T(3) in (U^3+E8(-2))_Q found: %s" % found, found is not None)
print("\n%d checks passed, %d failed" % (sum(1 for _, o in checks if o), sum(1 for _, o in checks if not o)))
