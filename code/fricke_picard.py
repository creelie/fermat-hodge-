"""
Point counts for the Picard number of one member of each Fricke family
(Remark V.10 of the paper): the member X_1 of A_N, the twist of the Fricke
universal curve at the pair {1, N^k}, N in {5, 7}.

The method is the one of van Luijk: for a prime l of good reduction and
q = l^i, the number of points of the smooth minimal model is

    #X(F_q) = sum over t in P^1(F_q) of W_t + q * (fibre corrections),

where W_t is the number of F_q-points of the Weierstrass fibre over t, and
the corrections (the components of the fibres I_N, III and I_0^* that are
rational over F_q, beyond the component meeting the zero section) are the
same as the trace of Frobenius on the trivial lattice divided by q, apart
from the classes of the zero section and of a fibre.  Hence the trace of
Frob_q on the orthogonal complement T of the trivial lattice (rank 6) is

    s_i = sum_t W_t - 1 - q^2 - 2 q,

with no bookkeeping of fibre types.  The characteristic polynomial P of
Frob_l on T is recovered from s_1, ..., s_m by Newton's identities and the
functional equation x^6 P(l^2 / x) = eps l^6 P(x), eps = +-1, which the
coefficients beyond the third determine and check.  If P(l x) has no
cyclotomic factor, no class of T is algebraic over the algebraic closure of
F_l, so rho(X_1) = 16 by the trivial lattice, and the very general member of
the family has Picard number 16, transcendental rank 6 and endomorphism
field exactly Q(sqrt(-N)).

The finite fields are handled by Zech logarithms, and the quadratic
character of g^k is (-1)^k.  The same count on the rational surface R_N
(where the complement of the trivial lattice is the Mordell-Weil part, of
rank 2) is run as a control: its traces are q times the trace of a
permutation of the two generators.
Run:  python3 -I fricke_picard.py          (about ten seconds)
"""
from fractions import Fraction
import sympy as sp

checks = []
def check(name, ok):
    checks.append(bool(ok))
    print(("PASS  " if ok else "FAIL  ") + name)

DATA = {
    7: dict(c4=[(49, 13, 1), (1, 5, 1)], c6=[(49, 13, 1), (-7, 70, 63, 14, 1)], Nk=49),
    5: dict(c4=[(5, 10, 1), (125, 22, 1)], c6=[(-1, 4, 1), (125, 22, 1), (125, 22, 1)], Nk=125),
}
# coefficient tuples are lowest degree first

def polymul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i+j] += x*y
    return r

class GF:
    """F_{l^n} by Zech logarithms.  Elements are logs 0..q-2, or None for 0."""
    def __init__(self, l, n):
        self.l, self.n, self.q = l, n, l**n
        q = self.q
        # find a primitive polynomial x^n - (c_{n-1} x^{n-1} + ... + c_0)
        import itertools
        for coeffs in itertools.product(range(l), repeat=n):
            if coeffs[0] == 0:
                continue
            # generate powers of x modulo the polynomial; vector as tuple of digits
            v = [0]*n; v[0] = 1
            seen = {}
            exp = []
            ok = True
            for k in range(q - 1):
                key = tuple(v)
                if key in seen:
                    ok = False; break
                seen[key] = k
                exp.append(key)
                # multiply by x
                top = v[-1]
                v = [0] + v[:-1]
                for i in range(n):
                    v[i] = (v[i] + top*coeffs[i]) % l
            if ok and tuple(v) == exp[0] and len(seen) == q - 1:
                break
        self.exp = exp                                   # log -> digit tuple
        self.log = {key: k for k, key in enumerate(exp)}  # digit tuple -> log
        zero = tuple([0]*n)
        self.zech = [None]*(q-1)
        one = exp[0]
        for k in range(q - 1):
            s = tuple((a + b) % l for a, b in zip(one, exp[k]))
            self.zech[k] = None if s == zero else self.log[s]
        # logs of the prime field elements 1..l-1
        self.const = [None] + [self.log[tuple([c] + [0]*(n-1))] for c in range(1, l)]
        self.neg1 = self.const[l - 1]                     # log of -1

    def add(self, a, b):
        if a is None: return b
        if b is None: return a
        z = self.zech[(b - a) % (self.q - 1)]
        return None if z is None else (a + z) % (self.q - 1)

    def mul(self, a, b):
        if a is None or b is None: return None
        return (a + b) % (self.q - 1)

    def cint(self, c):
        return self.const[c % self.l]

    def evalpoly(self, coeffs, tlog):
        """value of a polynomial with integer coefficients at the element with log tlog."""
        r = None
        for c in reversed(coeffs):
            r = self.add(self.mul(r, tlog), self.cint(c))
        return r

def weierstrass_count(F, a, b):
    """q + 1 + sum_x chi(x^3 + a x + b) with chi(g^k) = (-1)^k."""
    q1 = F.q - 1
    add, zech = F.add, F.zech
    total = F.q + 1
    # x = 0
    v = b
    if v is not None:
        total += 1 - 2*(v & 1)
    for k in range(q1):
        x3 = (3*k) % q1
        ax = None if a is None else (a + k) % q1
        v = add(x3, ax)
        v = add(v, b)
        if v is not None:
            total += 1 - 2*(v & 1)
    return total

def traces(N, l, imax, twist):
    """s_i for i = 1..imax: traces of Frob_{l^i} on the complement of the trivial lattice."""
    d = DATA[N]
    c4 = [1]
    for f in d['c4']: c4 = polymul(c4, list(f))
    c6 = [1]
    for f in d['c6']: c6 = polymul(c6, list(f))
    A = [-27*c for c in c4]; B = [-54*c for c in c6]
    if twist:
        u = polymul([-1, 1], [-d['Nk'], 1])
        A = polymul(A, polymul(u, u)); B = polymul(B, polymul(u, polymul(u, u)))
    out = []
    for i in range(1, imax + 1):
        F = GF(l, i)
        q = F.q
        total = 0
        # t = 0
        total += weierstrass_count(F, F.cint(A[0]), F.cint(B[0]))
        for k in range(q - 1):
            total += weierstrass_count(F, F.evalpoly(A, k), F.evalpoly(B, k))
        # t = infinity: leading coefficients
        total += weierstrass_count(F, F.cint(A[-1]), F.cint(B[-1]))
        out.append(total - 1 - q*q - 2*q)
    return out

def charpoly_from_traces(s, l, dim=6):
    """Newton's identities; returns the coefficients of x^dim - e1 x^(dim-1) + ... as Fractions."""
    e = [Fraction(1)]
    for k in range(1, len(s) + 1):
        ek = Fraction(0)
        for i in range(1, k + 1):
            ek += (-1)**(i-1) * e[k-i] * s[i-1]
        e.append(ek / k)
    return e

def complete_with_functional_equation(e, l, dim=6):
    """coefficients c_j of P(x) = sum c_j x^(dim-j), c_j = (-1)^j e_j for j <= m, and
    c_(dim-j) = eps l^(2(dim/2 - j)) c_j; returns (eps, list of c) or None if inconsistent."""
    m = len(e) - 1
    results = []
    for eps in (1, -1):
        c = [None]*(dim + 1)
        for j in range(m + 1):
            c[j] = (-1)**j * e[j]
        ok = True
        for j in range(dim + 1):
            k = dim - j
            val = eps * Fraction(l)**(2*(dim//2 - j)) * c[j] if c[j] is not None else None
            if val is None:
                continue
            if c[k] is None:
                c[k] = val
            elif c[k] != val:
                ok = False
        if ok and all(v is not None for v in c):
            results.append((eps, c))
    return results

x = sp.symbols('x')
def report(N, l, imax):
    print(f"-- N = {N}, l = {l}, traces of Frob_{{l^i}} on T for i <= {imax}")
    s = traces(N, l, imax, twist=True)
    print("      s_i =", s)
    e = charpoly_from_traces(s, l)
    cands = complete_with_functional_equation(e, l)
    check(f"N={N}, l={l}: the traces determine the sign of the functional equation (the middle coefficient is nonzero)",
          len(cands) == 1 and e[3] != 0)
    eps, c = cands[0]
    P = sum(sp.Rational(cj.numerator, cj.denominator) * x**(6 - j) for j, cj in enumerate(c))
    check(f"N={N}, l={l}: eps = +1 and P has integer coefficients",
          eps == 1 and all(sp.Rational(cf).q == 1 for cf in sp.Poly(P, x).all_coeffs()))
    Q = sp.expand(P.subs(x, l*x) / l**6)      # eigenvalues divided by l
    print(f"      P(x) =", sp.expand(P))
    print(f"      P(l x)/l^6 =", Q)
    cyclo = [n for n in range(1, 31) if sp.gcd(sp.Poly(Q, x), sp.Poly(sp.cyclotomic_poly(n, x), x)).degree() > 0]
    check(f"N={N}, l={l}: no root of P is l times a root of unity (cyclotomic factors of P(l x): {cyclo}), so rho(X_1) = 16",
          not cyclo)
    K = sp.sqrt(-N)
    fl = sp.factor_list(Q, extension=K)[1]
    print(f"      factorisation over Q(sqrt(-{N})):", sp.factor(Q, extension=K))
    check(f"N={N}, l={l}: P(l x)/l^6 is irreducible over Q and splits as g gbar, deg g = 3, over Q(sqrt(-{N})) (Frobenius commutes with f^*)",
          sp.Poly(Q, x).is_irreducible and len(fl) == 2 and all(sp.Poly(g, x).degree() == 3 for g, _ in fl))

def inert(N, l, imax):
    s = traces(N, l, imax, twist=True)
    print(f"-- N = {N}, l = {l} inert in Q(sqrt(-{N})): s_i = {s}")
    check(f"N={N}, l={l}: Frobenius exchanges the two eigenspaces of f^*, so the odd traces vanish",
          all(s[i] == 0 for i in range(0, imax, 2)))

# control: the rational surfaces R_N, complement of the trivial lattice = Mordell-Weil part of rank 2
for N, l in ((7, 5), (5, 7)):
    s = traces(N, l, 2, twist=False)
    check(f"control R_{N}, l={l}: the traces {s} on the Mordell-Weil part are q times the trace of a permutation of two generators",
          all(abs(si) <= 2*l**(i+1) and si % l**(i+1) == 0 for i, si in enumerate(s)))

# split primes: -7 = 4^2 mod 11, -5 = 3^2 mod 7
report(7, 11, 3)
report(5, 7, 4)
# inert primes: -7 is not a square mod 5, -5 is not a square mod 11
inert(7, 5, 3)
inert(5, 11, 3)

fails = sum(1 for c in checks if not c)
print(f"fricke_picard: {len(checks) - fails} checks passed, {fails} failed")
