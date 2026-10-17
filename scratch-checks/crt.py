import sys, math
from fractions import Fraction
def small_ratio(r, p, B=13):
    best = None
    for s in range(1, B):
        for a in range(-36, 37):
            if a == 0: continue
            if (a - r*s) % p == 0 and math.gcd(a, s) == 1:
                if best is None or abs(a)*s < abs(best.numerator)*best.denominator: best = Fraction(a, s)
    return best
def order(x, N): return N // math.gcd(x, N)
def moves(xs, N):
    S = set(xs); out = []
    for x in xs:
        f = order(x, N)
        if f % 2 == 0 and (-2*x) % N in S and (2*x) % N != 0: out.append('c')
        if f % 2 == 0 and (2*x + N//2) % N in S and (2*x+N//2) % N != x: out.append('d')
    return out
for fn in sys.argv[1:]:
    p = int(fn.split('_')[1].split('.')[0])
    N = 6*p
    for line in open(fn):
        w = line.split()
        xs = [int(t.split('/')[0]) for t in w[5:]]
        mv = moves(xs, N)
        x0 = xs[0]
        desc = []
        for x in xs:
            r = small_ratio(x * pow(x0, -1, p) % p, p)
            desc.append('(%d,%s)' % (x % 6, r))
        print(p, 'n=%d' % len(xs), 'MV' if mv else '--', ' '.join(desc))
