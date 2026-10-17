"""Filter local configurations (loc3 output) by the moves (c), (d) and test the
compound move: full T-transform, then greedy sigma_p moves on fibres of
elements of order e*.  Elements live in Z/e, e = 2e*, scaled by m/e.
usage: python3 compound.py D35.txt 35"""
import sys
from math import gcd
from collections import Counter

def primes(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: ps.append(n)
    return ps

def lift(t, v, es):
    e = 2 * es
    want = 1 if t == 'F' else 0
    for u in (v, v + es):
        if u % 2 == want: return u % e
    raise ValueError

def order(y, e):
    return e // gcd(y, e)

def depair(c, e):
    c = +c
    for y in list(c):
        while c[y] > 0 and c[(-y) % e] > 0 and (y != (-y) % e or c[y] >= 2):
            c[y] -= 1; c[(-y) % e] -= 1
    return +c

def compound(toks, es, verbose=False):
    e = 2 * es
    c = Counter()
    tops = []
    for t, v in toks:
        u = lift(t, v, es)
        if t == 'F': tops.append(u)
        else: c[u] += 1
    for u in tops:
        c[(-u + es) % e] += 1; c[(2 * u) % e] += 1; c[es] += 1
    c = depair(c, e)
    hist = [sum(c.values())]
    ps = [p for p in primes(es)]
    changed = True
    while changed:
        changed = False
        for p in ps:
            for x in sorted(c):
                if order(x, e) != es: continue
                fib = [(x + j * (e // p)) % e for j in range(p)]
                S = [y for y in fib if c[y] > 0]
                k = len(S)
                if 2 * k >= p + 1:
                    for y in S: c[y] -= 1
                    for y in fib:
                        if y not in S: c[(-y) % e] += 1
                    c[(p * x) % e] += 1
                    c = depair(c, e)
                    hist.append(sum(c.values()))
                    changed = True
                    break
            if changed: break
    return sum(c.values()), hist, c

def main():
    fn, es = sys.argv[1], int(sys.argv[2])
    for line in open(fn):
        if not line.startswith('C'): continue
        n = int(line.split()[1][2:])
        toks = [(w[0], int(w[1:])) for w in line.split(':')[1].split()]
        F = Counter(); E = Counter()
        for t, v in toks:
            (F if t == 'F' else E)[v] += 1
        movec = any(F[v] and E[(-2 * v) % es] for v in list(F))
        moved = any(F[v] and F[(2 * v) % es] for v in list(F))
        if movec or moved:
            continue
        size, hist, c = compound(toks, es)
        low = 6 - n
        tag = 'OK' if size + low <= 6 else 'STUCK'
        print(tag, es, ' '.join(t + str(v) for t, v in toks), 'low', low, 'sizes', hist)

main()
