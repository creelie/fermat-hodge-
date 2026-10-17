"""Consistency check for the identification of the Picard-13 specialisations of the
van Geemen-Schuett Q(zeta_9)^+ family with K3 surfaces of Mumford type.

Prediction (derived in report.md, Section 5): with F = Q(theta), theta = zeta_9 + zeta_9^{-1},
theta^3 - 3 theta + 1 = 0, and D = (-1, -theta)_F (the quaternion algebra over F ramified exactly
at the two real places where theta > 0), the transcendental space of the very general member of
the family, T_Q = (U + A_2(-1)^4)^perp in Lambda_Q, is Q-isometric to the trace form
      Tr_{F/Q}( -theta * nrd_D ),   a form of rank 12.
We compare rank, signature, discriminant and Hasse invariants at all primes up to 60 (the only
primes at which anything can happen are 2 and 3; the others are listed as a sanity check).
For contrast the same invariants are computed for the 'wrong' algebra (-1, theta)_F scaled to the
right signature, which should fail to match.
Run: python3 check_zeta9.py
"""
import sympy as sp
from sympy import symbols, Poly, Rational, factorint, legendre_symbol
th = symbols('th')
P = Poly(th**3 - 3*th + 1, th)

def red(e):
    return Poly(sp.expand(e), th).rem(P).as_expr()
def tr(e):
    e = red(e)
    cols = []
    for b in [1, th, th**2]:
        r = Poly(red(e*b), th)
        cols.append([r.coeff_monomial(th**k) for k in range(3)])
    return sp.nsimplify(sum(cols[k][k] for k in range(3)))

def trace_form(c, a, b):
    """Gram matrix of Tr_{F/Q}(c * nrd) on the quaternion algebra (a,b)_F with basis
    theta^m * {1, i, j, k}; nrd = <1, -a, -b, ab>."""
    diag = [1, -a, -b, a*b]
    basis = [(m, s) for s in range(4) for m in range(3)]
    G = sp.zeros(12, 12)
    for p_, (m, s) in enumerate(basis):
        for q_, (n, t) in enumerate(basis):
            if s == t:
                G[p_, q_] = tr(c*diag[s]*th**(m+n))
    return G

def diagonalize(G):
    G = sp.Matrix(G); n = G.shape[0]; vecs = []; D = []
    for i in range(n):
        v = sp.Matrix([1 if k == i else 0 for k in range(n)])
        for (w, d) in vecs:
            v = v - ((w.T*G*v)[0]/d)*w
        d = (v.T*G*v)[0]
        if d == 0:
            for j in range(i+1, n):
                u = sp.Matrix([1 if k == j else 0 for k in range(n)])
                for (w, dd) in vecs: u = u - ((w.T*G*u)[0]/dd)*w
                if (v.T*G*u)[0] != 0:
                    v = v + u; d = (v.T*G*v)[0]; break
        vecs.append((v, d)); D.append(sp.Rational(d))
    return D

def sqfree(r):
    r = sp.Rational(r); s = 1
    for n in (abs(r.p), r.q):
        for p, e in factorint(n).items():
            if e % 2: s *= p
    return s if r > 0 else -s

def hilbert(a, b, p):
    a = sp.Rational(a); b = sp.Rational(b)
    val = lambda r: sp.multiplicity(p, r.p) - sp.multiplicity(p, r.q)
    al, be = val(a), val(b)
    u = a/sp.Integer(p)**al; v = b/sp.Integer(p)**be
    if p != 2:
        leg = lambda r: legendre_symbol((r.p*pow(r.q, -1, p)) % p, p)
        return (-1)**(((p-1)//2)*al*be) * leg(u)**be * leg(v)**al
    m8 = lambda r: (r.p*pow(r.q, -1, 8)) % 8
    e = lambda m: ((m-1)//2) % 2; w = lambda m: ((m*m-1)//8) % 2
    return (-1)**((e(m8(u))*e(m8(v)) + al*w(m8(v)) + be*w(m8(u))) % 2)

def invariants(D, primes):
    sig = (sum(1 for d in D if d > 0), sum(1 for d in D if d < 0))
    disc = sqfree(sp.prod(D))
    eps = {}
    for p in primes:
        e = 1
        for i in range(len(D)):
            for j in range(i+1, len(D)):
                e *= hilbert(D[i], D[j], p)
        eps[p] = int(sp.nsimplify(e))
    return sig, disc, eps

def complement_invariants(V, W, primes):
    """Invariants of W' with V = W + W' (Witt), from diagonal lists."""
    sV, dV, eV = invariants(V, primes); sW, dW, eW = invariants(W, primes)
    sig = (sV[0]-sW[0], sV[1]-sW[1]); disc = sqfree(sp.Rational(dV)/dW)
    eps = {p: int(eV[p]*eW[p]*hilbert(dW, disc, p)) for p in primes}
    return sig, disc, eps

primes = list(sp.primerange(2, 60))
# K3 lattice over Q and Pic = U + A_2(-1)^4 ;  A_2(-1) = [[-2,1],[1,-2]] ~ <-2, -3/2>
Lam = [1]*3 + [-1]*19
Pic = [1, -1] + [-2, Rational(-3, 2)]*4
T_target = complement_invariants(Lam, Pic, primes)
print("T_Q = (U + A_2(-1)^4)^perp :  signature, d, Hasse =", T_target)

RESULTS = []
roots = sorted(sp.Poly(th**3 - 3*th + 1, th).nroots())
print("real embeddings of theta:", roots)

for label, (c, a, b) in {
    "predicted  D=(-1,-theta), c=-theta": (-th, -1, -th),
    "contrast   D=(-1, theta), c= theta": ( th, -1,  th),
    "contrast   D=(-1,-theta), c=-theta*(theta-2) (wrong sign pattern at infinity)": (-th*(th-2), -1, -th),
    "contrast   D=(-theta, -theta+1)": ((1-th)*th, -th, 1-th),
}.items():
    G = trace_form(c, a, b)
    inv = invariants(diagonalize(G), primes)
    print(f"{label}: signature, d, Hasse = {inv}   MATCH={inv == T_target}")
    RESULTS.append((label.startswith("predicted"), inv == T_target))

# Discriminating power: algebras (-1, b) with b = -theta*u, u totally positive, have the same real
# ramification as D but may ramify at finite places; then the trace form must differ at some prime.
print("\nSearch over b = -theta*u, u = x + y theta + z theta^2 totally positive, |x|,|y|,|z| <= 2:")
seen = {}
import itertools
for x, y, z in itertools.product(range(-2, 3), repeat=3):
    u = x + y*th + z*th**2
    if u == 0: continue
    vals = [u.subs(th, r) for r in roots]
    if not all(v > 0 for v in vals): continue
    b = -th*u
    G = trace_form(b, -1, b)
    inv = invariants(diagonalize(G), primes)
    key = (inv[0], inv[1], tuple(sorted(inv[2].items())))
    seen.setdefault(key, []).append(str(sp.expand(u)))
for key, us in seen.items():
    bad = {p: e for p, e in key[2] if e != 1}
    print(f"  signature {key[0]}, d={key[1]}, Hasse -1 at {bad}: u in {us[:6]}{' ...' if len(us)>6 else ''}  MATCH={ (key[0], key[1], dict(key[2])) == T_target }")

# the predicted algebra matches and every contrast fails; the search finds the target invariants
# exactly for b = -theta*u with u a totally positive square class giving the same Hasse data
assert all(pred == match for pred, match in RESULTS), RESULTS
assert any((k[0], k[1], dict(k[2])) == T_target for k in seen), "target invariants not found in the search"
print("zeta9_invariants: PASS")
