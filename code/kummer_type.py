"""kummer_type.py -- the criterion of Proposition V.16 (K3 surfaces of Kummer
type over Q) against a direct search.

A rational quadratic space T of signature (2, r-2) embeds isometrically in
U_Q^3 = H^2(A, Q) of an abelian surface if and only if r <= 3, or r = 4 and
eps_p(T) = (-1,-1)_p at every prime p at which d(T) is a square in Q_p, or
r = 5 and eps_p(T) = (-1,-1)_p at every prime p.  Hilbert symbols and Hasse
invariants eps = prod_{i<j} (a_i, a_j) follow Serre, A Course in Arithmetic,
Chapters III and IV.  The direct search looks for a complement W over a box of
diagonal coefficients and compares T + W with U^3 by rank, signature,
discriminant and Hasse invariants, which classify rational quadratic spaces.
The program also computes the discriminants (mod squares) of the
transcendental spaces of the Fricke surfaces of Theorem V.9 and of the two
families of Varesco, and the primes at which the two failing examples of
Remark V.17 fail.  Requires sympy (for factorint only).
"""
from fractions import Fraction
import itertools
import sys
import sympy

checks = []


def check(name, ok):
    checks.append(ok)
    print(("PASS  " if ok else "FAIL  ") + name)


def val(a, p):
    a = Fraction(a)
    v = 0
    n, d = a.numerator, a.denominator
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v, Fraction(n, d)


def legendre(u, p):
    u = Fraction(u)
    n = (u.numerator * pow(u.denominator, -1, p)) % p
    return 1 if pow(n, (p - 1) // 2, p) == 1 else -1


def hilbert(a, b, p):
    """Hilbert symbol (a, b)_p, p a prime or 'inf'."""
    a, b = Fraction(a), Fraction(b)
    assert a != 0 and b != 0
    if p == 'inf':
        return -1 if (a < 0 and b < 0) else 1
    va, ua = val(a, p)
    vb, ub = val(b, p)
    if p == 2:
        def e(u):
            n = (u.numerator * pow(u.denominator, -1, 8)) % 8
            return ((n - 1) // 2) % 2

        def w(u):
            n = (u.numerator * pow(u.denominator, -1, 8)) % 8
            return ((n * n - 1) // 8) % 2
        s = e(ua) * e(ub) + va * w(ub) + vb * w(ua)
        return -1 if s % 2 else 1
    s = (-1) ** (va * vb * ((p - 1) // 2)) * legendre(ua, p) ** vb * legendre(ub, p) ** va
    return s


def primes_of(diag):
    ps = {2}
    for a in diag:
        a = Fraction(a)
        for n in (abs(a.numerator), a.denominator):
            ps |= set(sympy.factorint(n).keys())
    return sorted(ps)


def hasse(diag, p):
    e = 1
    for i in range(len(diag)):
        for j in range(i + 1, len(diag)):
            e *= hilbert(diag[i], diag[j], p)
    return e


def disc(diag):
    d = Fraction(1)
    for a in diag:
        d *= Fraction(a)
    return d


def squarefree(d):
    """The class of a nonzero rational d in Q^x / Q^{x2}, as a squarefree integer."""
    d = Fraction(d)
    n = d.numerator * d.denominator
    s = -1 if n < 0 else 1
    out = 1
    for p, k in sympy.factorint(abs(n)).items():
        if k % 2:
            out *= p
    return s * out


def is_square_in_Qp(d, p):
    d = Fraction(d)
    if p == 'inf':
        return d > 0
    v, u = val(d, p)
    if v % 2:
        return False
    if p == 2:
        return (u.numerator * pow(u.denominator, -1, 8)) % 8 == 1
    return legendre(u, p) == 1


def failing_primes(diag):
    """Primes at which the local condition of criterion (c) fails."""
    r = len(diag)
    d = disc(diag)
    bad = []
    for p in primes_of(diag):
        if r == 5 and hasse(diag, p) != hilbert(-1, -1, p):
            bad.append(p)
        if r == 4 and is_square_in_Qp(d, p) and hasse(diag, p) != hilbert(-1, -1, p):
            bad.append(p)
    return bad


def embeds_in_U3(diag):
    """Criterion (c): does T of signature (2, r-2) embed isometrically in U_Q^3?"""
    r = len(diag)
    assert sum(1 for a in diag if a > 0) == 2
    if r >= 6:
        return False
    if r <= 3:
        return True
    return not failing_primes(diag)


def same_space(A, B, ps):
    """Hasse-Minkowski: equal rank, signature, discriminant class and Hasse invariants."""
    if len(A) != len(B):
        return False
    if sum(1 for a in A if a > 0) != sum(1 for b in B if b > 0):
        return False
    dq = disc(A) / disc(B)
    for p in ps + ['inf']:
        if not is_square_in_Qp(dq, p):
            return False
        if hasse(A, p) != hasse(B, p):
            return False
    return True


U3 = [1, -1, 1, -1, 1, -1]


def complement(diag, V=U3, box=30):
    """A diagonal W with T + W = V over Q, found by search, or None."""
    k = len(V) - len(diag)
    ps = sorted(set(primes_of(diag)) | set(primes_of(V)) | {3, 5, 7})
    coeffs = [c for c in range(-box, box + 1) if c != 0]
    for W in itertools.product(coeffs, repeat=k):
        if same_space(list(diag) + list(W), V, ps):
            return list(W)
    return None


# (A) the invariants of U^3
check("U^3 has discriminant -1", squarefree(disc(U3)) == -1)
check("U^3 has Hasse invariant (-1,-1)_p at p = 2, 3, 5, 7, 11, 13",
      all(hasse(U3, p) == hilbert(-1, -1, p) for p in (2, 3, 5, 7, 11, 13)))
check("(-1,-1)_2 = -1 and (-1,-1)_p = 1 for odd p < 50",
      hilbert(-1, -1, 2) == -1 and all(hilbert(-1, -1, p) == 1 for p in sympy.primerange(3, 50)))

# (B) the criterion against the search, ranks 4 and 5
tests = {
    'U^2 + <-2>': [1, -1, 1, -1, -2],
    'U^2 + <-6>': [1, -1, 1, -1, -6],
    'U + <2,-2,-2>': [1, -1, 2, -2, -2],
    '<2,2,-2,-2,-2>': [2, 2, -2, -2, -2],
    '<2,6,-2,-2,-2>': [2, 6, -2, -2, -2],
    '<2,2,-2,-6,-6>': [2, 2, -2, -6, -6],
    'U^2 + <-4>': [1, -1, 1, -1, -4],
    'U + <2,-2,-6>': [1, -1, 2, -2, -6],
    '<2,2,-2,-10,-10>': [2, 2, -2, -10, -10],
    '<2,2,-2,-2>': [2, 2, -2, -2],
    '<2,2,-2,-6>': [2, 2, -2, -6],
    '<2,6,-2,-2>': [2, 6, -2, -2],
    '<2,10,-2,-2>': [2, 10, -2, -2],
    'U + <2,-6>': [1, -1, 2, -6],
}
agree = 0
results = {}
for name, T in tests.items():
    crit = embeds_in_U3(T)
    W = complement(T)
    results[name] = (crit, W)
    ok = crit == (W is not None)
    agree += ok
    print("      %-18s rank %d  criterion=%-5s  complement=%s" % (name, len(T), crit, W))
check("criterion (c) agrees with the search on %d of %d spaces" % (agree, len(tests)), agree == len(tests))
check("U^2 + <-2> and U + <2,-2,-2> are of Kummer type",
      results['U^2 + <-2>'][0] and results['U + <2,-2,-2>'][0])
check("<2,2,-2,-6,-6> and <2,6,-2,-2,-2> are not, and fail at p = 2 and p = 3",
      failing_primes([2, 2, -2, -6, -6]) == [2, 3] and failing_primes([2, 6, -2, -2, -2]) == [2, 3])
check("every space of rank 4 in the list is of Kummer type",
      all(results[n][0] for n in tests if len(tests[n]) == 4))
T4 = [2, 2, -6, -6]
check("<2,2,-6,-6> (rank 4, d = 1) fails at p = 2 and p = 3, and the search finds no complement",
      failing_primes(T4) == [2, 3] and complement(T4) is None)
# counts over a box of coefficients: how often the condition holds
vals = [1, 2, 3, 5, 6, 10, 15, 30]
c4 = {True: 0, False: 0}
for a, b in itertools.combinations_with_replacement(vals, 2):
    for c, d in itertools.combinations_with_replacement(vals, 2):
        c4[embeds_in_U3([a, b, -c, -d])] += 1
c5 = {True: 0, False: 0}
for a, b in itertools.combinations_with_replacement(vals, 2):
    for c, d, e in itertools.combinations_with_replacement(vals, 3):
        c5[embeds_in_U3([a, b, -c, -d, -e])] += 1
print("      rank 4 over the box: %d of Kummer type, %d not; rank 5: %d and %d" % (c4[True], c4[False], c5[True], c5[False]))
check("rank 4: 1084 of 1296 diagonal spaces over the box embed; rank 5: 1304 of 4320",
      (c4[True], c4[False], c5[True], c5[False]) == (1084, 212, 1304, 3016))
check("the primes at which (c) fails come in pairs (product formula) for every space of the box",
      all(len(failing_primes([a, b, -c, -d, -e])) % 2 == 0
          for a, b in itertools.combinations_with_replacement(vals, 2)
          for c, d, e in itertools.combinations_with_replacement(vals, 3)))
check("rank 6 of signature (2,4) never embeds (signature)", not embeds_in_U3([1, -1, 1, -1, -2, -2]))

# (C) discriminants mod squares: d(T) = -d(NS) for a primitive sublattice of the K3 lattice (d = -1)
dU, dA1, dA4, dA6, dD4 = -1, -2, 5, 7, 4          # negative definite root lattices
dNS5 = dU * dA4 * dA1 ** 2 * dD4 ** 2             # U + A4 + A1^2 + D4^2
dNS7 = dU * dA6 * dD4 ** 2                        # U + A6 + D4^2
dT5, dT7 = squarefree(Fraction(-1, dNS5)), squarefree(Fraction(-1, dNS7))
check("Fricke N = 5: d(T) = 5 mod squares", dT5 == 5)
check("Fricke N = 7: d(T) = 7 mod squares", dT7 == 7)
dSix = squarefree(disc([1, -1, 1, -1, -2, -2]))   # six lines, U_Q^2 + <-2>^2
dILP = squarefree(disc([1, -1, 1, -1, -6, -2]))   # 15-nodal, U_Q^2 + <-6> + <-2>
check("Varesco's families: d(T) = 1 and 3 mod squares", (dSix, dILP) == (1, 3))
check("the four discriminant classes 1, 3, 5, 7 are distinct", len({dSix, dILP, dT5, dT7}) == 4)

n = len(checks)
f = n - sum(checks)
print("kummer_type: %d checks passed, %d failed" % (n - f, f))
sys.exit(0 if f == 0 else 1)
