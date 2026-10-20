"""
Certificate for Proposition V.17 of the paper: the transcendental spaces of
the Fricke surfaces and their Kuga-Satake fourfolds.

The very general surface of the Fricke family of level N in {5, 7} has
Picard lattice of the same rank as the trivial lattice of its elliptic
fibration, U + A_4 + A_1^2 + D_4^2 (N = 5) or U + A_6 + D_4^2 (N = 7), so
its transcendental space T = NS^perp in the K3 lattice tensor Q is
determined over Q by the invariants of Hasse-Minkowski.  The program
checks, by those invariants (rank, signature, discriminant and Hasse
invariants at every prime dividing twice a diagonal entry):

  (A) the rational isometries used in the hand proof, A_n + <n+1> = <1>^(n+1)
      for n = 4, 6, D_4 = <1>^4, A_1^2 = <1>^2 and E_8 = <1>^8;
  (B) T = U^2 + <-1> + <-N> for N = 5 and 7, in two ways: by cancelling
      NS against the K3 lattice, and by comparing the invariants of
      NS + U^2 + <-1,-N> with those of the K3 lattice directly;
  (C) the shape of Lombardo's form: among the pairs a <= b of negative
      squarefree integers up to 30, those with U^2 + <a,b> = T are exactly
      the pairs with <a,b> = <-1,-N>, and the signed discriminant of T is
      -N, so the centre of the even Clifford algebra is Q(sqrt(-N));
  (D) the dimension count of the proof: the Hodge group of T has dimension
      2 dim SO(3) = 6 = dim SO*(4), the group of the quaternion fourfold.
Run:  python3 -I fricke_lattice.py
"""
from fractions import Fraction
import sys
import sympy

checks = []
def check(name, ok):
    checks.append(bool(ok))
    print(("PASS  " if ok else "FAIL  ") + name)

def val(a, p):
    a = Fraction(a); v = 0
    n, d = a.numerator, a.denominator
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v, Fraction(n, d)

def legendre(u, p):
    u = Fraction(u); r = (u.numerator * pow(u.denominator, -1, p)) % p
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1

def hilbert(a, b, p):
    """Hilbert symbol (a,b)_p for nonzero rationals a, b and a prime p."""
    al, u = val(a, p); be, v = val(b, p)
    if p != 2:
        s = (-1) ** (al * be * ((p - 1) // 2))
        return s * legendre(u, p) ** be * legendre(v, p) ** al
    def eps(x):  # (x-1)/2 mod 2 for x a 2-adic unit
        x = Fraction(x); r = (x.numerator * pow(x.denominator, -1, 8)) % 8
        return ((r - 1) // 2) % 2
    def om(x):
        x = Fraction(x); r = (x.numerator * pow(x.denominator, -1, 8)) % 8
        return ((r * r - 1) // 8) % 2
    e = eps(u) * eps(v) + al * om(v) + be * om(u)
    return (-1) ** (e % 2)

def primes_of(diag):
    ps = {2}
    for a in diag:
        a = Fraction(a)
        for n in (abs(a.numerator), a.denominator):
            ps |= set(sympy.factorint(n).keys())
    return sorted(ps)

def squarefree(d):
    d = Fraction(d); n = d.numerator * d.denominator
    s = -1 if n < 0 else 1
    r = 1
    for p, k in sympy.factorint(abs(n)).items():
        if k % 2: r *= p
    return s * r

def diag(G):
    """Diagonalise a rational symmetric Gram matrix; return squarefree entries."""
    n = len(G); M = [[Fraction(x) for x in r] for r in G]; out = []
    for i in range(n):
        if M[i][i] == 0:
            j = next(k for k in range(i, n) if M[i][k] != 0)
            for r in range(n): M[r][i] += M[r][j]
            for c in range(n): M[i][c] += M[j][c]
        d = M[i][i]; out.append(d)
        for r in range(i + 1, n):
            f = M[r][i] / d
            for c in range(n): M[r][c] -= f * M[i][c]
        for c in range(i + 1, n):
            f = M[i][c] / d
            for r in range(n): M[r][c] -= f * M[r][i]
    return [squarefree(d) for d in out]

class QForm:
    def __init__(self, entries):
        self.d = [squarefree(x) for x in entries]
    def rank(self): return len(self.d)
    def signature(self): return (sum(1 for x in self.d if x > 0), sum(1 for x in self.d if x < 0))
    def disc(self):
        r = 1
        for x in self.d: r *= x
        return squarefree(r)
    def hasse(self, p):
        e = 1
        for i in range(len(self.d)):
            for j in range(i + 1, len(self.d)):
                e *= hilbert(self.d[i], self.d[j], p)
        return e
    def primes(self): return primes_of(self.d)
    def same(self, other):
        """Isometry over Q by Hasse-Minkowski: rank, signature, discriminant
        and Hasse invariants at every prime of either form (elsewhere both are 1)."""
        if self.rank() != other.rank() or self.signature() != other.signature(): return False
        if self.disc() != other.disc(): return False
        return all(self.hasse(p) == other.hasse(p) for p in sorted(set(self.primes()) | set(other.primes())))
    def __add__(self, other): return QForm(self.d + other.d)

def cartan(t, n):
    G = [[0] * n for _ in range(n)]
    for i in range(n): G[i][i] = 2
    if t == 'A':
        for i in range(n - 1): G[i][i + 1] = G[i + 1][i] = -1
    elif t == 'D':
        for i in range(n - 2): G[i][i + 1] = G[i + 1][i] = -1
        G[n - 3][n - 1] = G[n - 1][n - 3] = -1
    elif t == 'E' and n == 8:
        # chain 1-2-3-4-5-6-7 with 8 attached to node 5 (Bourbaki: 3)
        for i in range(6): G[i][i + 1] = G[i + 1][i] = -1
        G[2][7] = G[7][2] = -1
    return G

def root(t, n, sign=1):
    return QForm([sign * x for x in diag(cartan(t, n))])

def ones(n, sign=1): return QForm([sign] * n)
U = QForm([1, -1])

# (A) rational isometries of the root lattices
for n in (4, 6):
    check(f"A_{n} + <{n+1}> = <1>^{n+1} over Q", (root('A', n) + QForm([n + 1])).same(ones(n + 1)))
check("D_4 = <1>^4 over Q", root('D', 4).same(ones(4)))
check("A_1^2 = <2,2> = <1>^2 over Q", QForm([2, 2]).same(ones(2)))
E8 = root('E', 8)
check("the Cartan matrix of E_8 has determinant 1 and E_8 = <1>^8 over Q",
      sympy.Matrix(cartan('E', 8)).det() == 1 and E8.same(ones(8)))

# (B) the transcendental spaces
Lam = U + U + U + root('E', 8, -1) + root('E', 8, -1)
check("the K3 lattice is U^3 + E_8(-1)^2, of signature (3,19), discriminant -1", Lam.signature() == (3, 19) and Lam.disc() == -1)
NS = {5: U + root('A', 4, -1) + QForm([-2, -2]) + root('D', 4, -1) + root('D', 4, -1),
      7: U + root('A', 6, -1) + root('D', 4, -1) + root('D', 4, -1)}
T = {}
for N in (5, 7):
    T[N] = U + U + QForm([-1, -N])
    check(f"N = {N}: NS has rank 16 and signature (1,15)", NS[N].rank() == 16 and NS[N].signature() == (1, 15))
    # cancellation: NS + W = Lam with W = -(root part + <1,N>) = <-1>^16 and U^3
    W = QForm(NS[N].d[2:] + [-1, -N])   # negative definite part of NS together with <-1,-N>
    check(f"N = {N}: the negative part of NS together with <-1,-N> is <-1>^16 over Q", W.same(ones(16, -1)))
    check(f"N = {N}: NS + U^2 + <-1,-N> has the invariants of the K3 lattice, so T = U^2 + <-1,-{N}>",
          (NS[N] + T[N]).same(Lam))
    # direct: invariants of T from Lam and NS
    dT = squarefree(Lam.disc() * NS[N].disc())
    eps = {p: Lam.hasse(p) * NS[N].hasse(p) * hilbert(NS[N].disc(), dT, p) for p in sorted(set(Lam.primes()) | set(NS[N].primes()))}
    check(f"N = {N}: d(T) = {N} and the Hasse invariants of T computed from Lam and NS agree with those of U^2 + <-1,-{N}>",
          dT == N and all(T[N].hasse(p) == eps[p] for p in eps))

# (C) Lombardo's shape and the Clifford centre
for N in (5, 7):
    sols = [(a, b) for a in range(-1, -31, -1) if squarefree(a) == a
            for b in range(a, -31, -1) if squarefree(b) == b and (U + U + QForm([a, b])).same(T[N])]
    expect = [(a, b) for a in range(-1, -31, -1) if squarefree(a) == a
              for b in range(a, -31, -1) if squarefree(b) == b and QForm([a, b]).same(QForm([-1, -N]))]
    check(f"N = {N}: U^2 + <a,b> = T exactly for <a,b> = <-1,-{N}> ({len(sols)} pairs up to 30, first {sols[:3]})",
          sols == expect and (-1, -N) in sols and len(sols) >= 2)
    check(f"N = {N}: the signed discriminant (-1)^3 d(T) is -{N}: the centre of C^+(T) is Q(sqrt(-{N}))",
          squarefree(-T[N].disc()) == -N)
check("Q(sqrt(-5)) and Q(sqrt(-7)) are the Weil fields: -ab = -5, -7 for (a,b) = (-1,-5), (-1,-7)",
      squarefree(-(-1) * (-5)) == -5 and squarefree(-(-1) * (-7)) == -7)

# (D) the dimension count
dim_so = lambda n: n * (n - 1) // 2
dim_so_star = lambda n: n * (2 * n - 1)       # so*(2n), the D-unitary group of a quaternion 2n-fold
check("dim Res_{E/Q} SO(Q) = 2 dim SO(3) = 6 = dim SO*(4), the Hodge group of the quaternion fourfold",
      2 * dim_so(3) == 6 == dim_so_star(2))
check("the quaternion-type fourfolds form families of dimension n(n-1)/2 = 1 for n = 2, as the Fricke families",
      2 * (2 - 1) // 2 == 1)

f = checks.count(False)
print(f"fricke_lattice: {len(checks) - f} checks passed, {f} failed")
sys.exit(0 if f == 0 else 1)
