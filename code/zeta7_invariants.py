"""Exact check for Theorem thm:zeta9 at n = 7 and for Proposition prop:cubicstop(i).

F = Q(theta), theta = zeta_7 + zeta_7^{-1}, theta^3 + theta^2 - 2 theta - 1 = 0, real embeddings
-1.802, -0.445, 1.247.  D_inf = (-1, theta)_F is ramified exactly at the two real places where
theta < 0.  The two-dimensional family y^2 = x^3 + b x + c_1 p_{7,a}(t) + c_0 (Dickson deformation
of family a) of Artebani-Sarti-Taki, Example 6.1) has very general Picard lattice U + E_8(-1), so
its transcendental space is U^2 + E_8(-1) over Q, and Steps 2-3 of the proof say it is
Tr_{F/Q}(theta nrd_{D_inf}) up to a totally positive scalar.  We compare rank, signature,
discriminant and Hasse invariants at all primes below 60 (only 2 and 7 can carry anything), both
directly and by Witt cancellation of U + E_8(-1) inside the K3 lattice; the contrasting algebras
with the same real ramification and finite ramification differ at 7 or 43.  We also verify the
Dickson identities p_{7,a}(v + a/v) = v^7 + (a/v)^7, p_{7,a}(mu t) = mu^7 p_{7,a/mu^2}(t) and the
t^5 coefficient of p_{7,a}(zeta t) - p_{7,a}(t) used in Step 1, and that 2 has order three in
(Z/7)^x/{+-1} and in (Z/9)^x/{+-1}, so that 2 is inert in both cubic fields.
Run: python3 -I zeta7_invariants.py
"""
import itertools, sympy as sp
from sympy import symbols, Poly, Rational, factorint, legendre_symbol

th = symbols('th')

def make_field(minpoly):
    P = Poly(minpoly, th)
    def red(e): return Poly(sp.expand(e), th).rem(P).as_expr()
    def tr(e):
        e = red(e); s = 0
        for k, b in enumerate([1, th, th**2]):
            s += Poly(red(e*b), th).coeff_monomial(th**k)
        return sp.nsimplify(s)
    return red, tr, sorted(P.nroots())

def trace_form(tr, c, a, b):
    """Gram matrix of Tr_{F/Q}(c nrd) on (a,b)_F, basis theta^m {1,i,j,k}, nrd = <1,-a,-b,ab>."""
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
        for (w, d) in vecs: v = v - ((w.T*G*v)[0]/d)*w
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
    disc = sqfree(sp.prod(D)); eps = {}
    for p in primes:
        e = 1
        for i in range(len(D)):
            for j in range(i+1, len(D)): e *= hilbert(D[i], D[j], p)
        eps[p] = int(e)
    return sig, disc, eps

def complement_invariants(V, W, primes):
    sV, dV, eV = invariants(V, primes); sW, dW, eW = invariants(W, primes)
    sig = (sV[0]-sW[0], sV[1]-sW[1]); disc = sqfree(sp.Rational(dV)/dW)
    return sig, disc, {p: int(eV[p]*eW[p]*hilbert(dW, disc, p)) for p in primes}

primes = list(sp.primerange(2, 60))
E8 = sp.Matrix([[2,-1,0,0,0,0,0,0],[-1,2,-1,0,0,0,0,0],[0,-1,2,-1,0,0,0,0],[0,0,-1,2,-1,0,0,0],
                [0,0,0,-1,2,-1,0,-1],[0,0,0,0,-1,2,-1,0],[0,0,0,0,0,-1,2,0],[0,0,0,0,-1,0,0,2]])
assert E8.det() == 1
dE8m = diagonalize(-E8)
U = [1, -1]
direct = invariants(U + U + dE8m, primes)
Lam = [1]*3 + [-1]*19
witt = complement_invariants(Lam, U + dE8m, primes)
print("U^2 + E_8(-1): direct", direct, " by Witt cancellation", witt)
assert direct == witt == ((2, 10), 1, {p: (-1 if p == 2 else 1) for p in primes})

red, tr, roots = make_field(th**3 + th**2 - 2*th - 1)
print("real embeddings of theta:", [round(float(r), 3) for r in roots])
assert sum(1 for r in roots if r > 0) == 1
pred = invariants(diagonalize(trace_form(tr, th, -1, th)), primes)
print("Tr(theta nrd_{(-1,theta)}):", pred, "MATCH", pred == direct)
assert pred == direct
for label, (c, a, b) in {"(-1,-theta), c=-theta": (-th, -1, -th),
                         "(-1,theta), c=-theta": (-th, -1, th)}.items():
    inv = invariants(diagonalize(trace_form(tr, c, a, b)), primes)
    print("contrast", label, inv); assert inv != direct
# algebras (-1, theta u), u totally positive: same real ramification; the finitely ramified ones differ
bad_primes = set(); matched = 0
for x, y, z in itertools.product(range(-2, 3), repeat=3):
    u = x + y*th + z*th**2
    if u == 0 or not all(u.subs(th, r) > 0 for r in roots): continue
    inv = invariants(diagonalize(trace_form(tr, th*u, -1, th*u)), primes)
    if inv == direct: matched += 1
    else:
        assert inv[0] == (2, 10) and inv[1] == 1
        bad_primes |= {p for p, e in inv[2].items() if e == -1}
print("competitors with the same real ramification: matched", matched, "; others differ at", sorted(bad_primes))
assert matched > 0 and bad_primes <= {7, 43} and 7 in bad_primes

# Dickson identities (Step 1 for n = 7) and the inertness of 2
v, a, t, mu, z = symbols('v a t mu z')
p7 = t**7 - 7*a*t**5 + 14*a**2*t**3 - 7*a**3*t
assert sp.expand(p7.subs(t, v + a/v) - v**7 - (a/v)**7) == 0
assert sp.expand(p7.subs(t, mu*t) - mu**7*p7.subs(a, a/mu**2)) == 0
diff = sp.Poly(sp.expand(p7.subs(t, z*t) - p7), t)
assert diff.coeff_monomial(t**7) == sp.expand(z**7 - 1) and diff.coeff_monomial(t**5) == sp.expand(-7*a*(z**5 - 1))
p9 = t**9 - 9*a*t**7 + 27*a**2*t**5 - 30*a**3*t**3 + 9*a**4*t
assert sp.expand(p9.subs(t, v + a/v) - v**9 - (a/v)**9) == 0
for n in (7, 9):
    k = 1; x = 2 % n
    while x not in (1, n - 1): x = (2*x) % n; k += 1
    assert k == 3, (n, k)
print("Dickson identities for n = 7, 9 hold; 2 has order three in (Z/7)^x/{+-1} and (Z/9)^x/{+-1}")
print("zeta7_invariants: PASS")
