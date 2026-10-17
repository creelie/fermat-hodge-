"""The four small patterns left by the local analysis at a top order 4e*
(e* in {5, 7, 11}): build every sextuple at the levels 20, 28, 44, 140 that
contains them, test balancedness, pairs, generation, splitness, and search a
chain of standard moves (sigma_{l,x}, T(x)) to a multiset of at most four
elements or a sextuple of smaller profile / lower level / split.
usage: python3 glob4.py"""
from math import gcd
from itertools import combinations_with_replacement as cwr
from collections import Counter

def units(M): return [t for t in range(1, M) if gcd(t, M) == 1]
def balanced(A, M):
    return all(sum((t * a) % M for a in A) == len(A) // 2 * M for t in units(M))
def order(y, M): return M // gcd(y, M)
def depair(c, M):
    c = Counter(c)
    for y in sorted(c):
        z = (-y) % M
        while c[y] > 0 and c[z] > 0 and (y != z or c[y] >= 2):
            c[y] -= 1; c[z] -= 1
    return +c
def haspair(A, M):
    c = Counter(A)
    return any(c[(-y) % M] > (1 if (-y) % M == y else 0) for y in c)
def split3(A, M):
    for i in range(6):
        for j in range(i+1, 6):
            for k in range(j+1, 6):
                if (A[i] + A[j] + A[k]) % M == 0: return True
    return False
def gen(A, M):
    g = M
    for a in A: g = gcd(g, a)
    return g == 1
def primes(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: ps.append(n)
    return ps
def sigmas(M):
    out = []
    for l in primes(M):
        d = M // l
        for i in range(1, d):
            if l == 2:
                out.append(('T', i, [i, i + M // 2, (-2 * i) % M, M // 2]))
            else:
                out.append(('s%d' % l, i, [i + j * d for j in range(l)] + [(-l * i) % M]))
    return out
def apply(c, sig, M):
    c = Counter(c); hit = 0; miss = []
    for y in sig:
        if c[y] > 0: c[y] -= 1; hit += 1
        else: miss.append(y)
    if hit == 0: return None
    for y in miss: c[(-y) % M] += 1
    return depair(c, M)
def profile(A, M): return sorted((order(a, M) for a in A), reverse=True)
def success(c, M, prof0):
    n = sum(c.values())
    if n <= 4: return 'direct'
    if n != 6: return None
    B = sorted(c.elements())
    if not gen(B, M): return 'lower level'
    if split3(B, M): return 'split'
    if profile(B, M) < prof0: return 'lower profile'
    return None
def search(A, M, depth=4, cap=10):
    S = sigmas(M); prof0 = profile(A, M)
    start = depair(Counter(A), M)
    frontier = [(start, [])]
    seen = {tuple(sorted(start.elements()))}
    for d in range(depth):
        nxt = []
        for c, path in frontier:
            for name, i, sig in S:
                c2 = apply(c, sig, M)
                if c2 is None or sum(c2.values()) > cap: continue
                key = tuple(sorted(c2.elements()))
                if key in seen: continue
                seen.add(key)
                p2 = path + [(name, i, key)]
                r = success(c2, M, prof0)
                if r: return r, p2
                nxt.append((c2, p2))
        frontier = nxt
    return None, None
def xel(M, es, sign, v):   # element of order 4e*, u = sign mod 4, u = v mod e*
    for u in range(1, 4 * es):
        if u % 4 == sign % 4 and u % es == v % es and gcd(u, 4 * es) == 1:
            return (M // (4 * es)) * u % M
def zel(M, es, v): return (M // es) * v % M
def canon(A, M):
    return min(tuple(sorted((t * a) % M for a in A)) for t in units(M))

cases = []
# (a) e* = 5 at M = 20 with three elements of 2-power order
M = 20
loc = [xel(M, 5, 1, 1), xel(M, 5, 1, 2), zel(M, 5, 3)]
for o in cwr([5, 10, 15], 3): cases.append(('(a) M=20', M, loc + list(o)))
# (c) e* = 7 at M = 28
M = 28
loc = [xel(M, 7, 1, 1), xel(M, 7, 1, 2), xel(M, 7, 1, 4)]
for o in cwr([7, 14, 21], 3): cases.append(('(c) M=28', M, loc + list(o)))
# (e) e* = 7 at M = 28
loc = [xel(M, 7, 1, 1), xel(M, 7, 1, 2), xel(M, 7, 1, 3), zel(M, 7, 4), zel(M, 7, 5)]
for o in [7, 14, 21]: cases.append(('(e) M=28', M, loc + [o]))
# (g) e* = 11 at M = 44
M = 44
cases.append(('(g) M=44', M, [xel(M, 11, 1, v) for v in (1, 2, 4, 8, 5)] + [zel(M, 11, 6)]))
# (a) + (c) at M = 140, both signs of the 7-part
M = 140
for s in (1, 3):
    cases.append(('(a)+(c) M=140 sign %d' % s, M,
                  [xel(M, 5, 1, 1), xel(M, 5, 1, 2), zel(M, 5, 3)] + [xel(M, 7, s, v) for v in (1, 2, 4)]))
for name, M, A in cases:
    A = sorted(A)
    b = balanced(A, M); hp = haspair(A, M); sp = split3(A, M); g = gen(A, M)
    tag = 'balanced' if b else 'not balanced'
    if not b or hp or sp or not g:
        print(name, A, tag, 'pair' if hp else '', 'split' if sp else '', '' if g else 'nongen')
        continue
    r, path = search(A, M)
    print(name, A, tag, 'canon', canon(A, M), '->', r)
    if path:
        for step in path: print('    ', step)
