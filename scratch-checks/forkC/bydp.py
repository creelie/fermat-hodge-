# Group the configurations of all L files by e' and by D' (the 2,3-part of the
# lcm of their orders), in canonical form at level D' e' (lex-min sorted tuple
# over the units of Z/(D'e')).  Checks that every file with D' | D carries the
# same set of forms with that D' (restriction to D'), and prints, for each e',
# the number of distinct configurations with each D' and the largest D seen.
import sys, glob, math, re
from collections import defaultdict
def part23(n):
    d = 1
    for p in (2, 3):
        while n % p == 0: n //= p; d *= p
    return d
def lcm(a, b): return a * b // math.gcd(a, b)
def canon(xs, Np):
    g = min(math.gcd(x, Np) for x in xs)
    best = None
    for x in set(xs):
        if math.gcd(x, Np) != g: continue
        o = Np // g; xr = x // g  # x = g xr, xr a unit mod o
        # units t mod Np with t xr = 1 mod o
        t0 = pow(xr, -1, o)
        for k in range(Np // o):
            t = t0 + k * o
            if math.gcd(t, Np) != 1: continue
            b = tuple(sorted(y * t % Np for y in xs))
            if best is None or b < best: best = b
    return best
files = defaultdict(dict)   # e -> D -> {Dp: set(forms)}
for fn in sorted(glob.glob('/dev/shm/tmpb/forkC/data/L_*_*_*.txt')):
    m = re.match(r'L_(\d+)_(\d+)_(\d+)\.txt$', fn.split('/')[-1])
    if not m: continue
    v, w, e = map(int, m.groups()); D = 2**v * 3**w; N = D * e
    byd = defaultdict(set)
    for line in open(fn):
        if not line.startswith('C'): continue
        els = [tuple(map(int, t.split('/'))) for t in line.split(':')[1].split()]
        L = 1
        for x, o in els: L = lcm(L, o)
        Dp = part23(L); Np = Dp * e; s = N // Np
        byd[Dp].add(canon([x // s for x, o in els], Np))
    files[e][D] = byd
for e in sorted(files):
    allf = defaultdict(set); bad = []
    for D, byd in files[e].items():
        for Dp, fs in byd.items(): allf[Dp] |= fs
    for D, byd in files[e].items():
        for Dp in allf:
            if D % Dp == 0 and byd.get(Dp, set()) != allf[Dp]: bad.append((D, Dp))
    print('e=%d maxD=%d' % (e, max(files[e])), ' '.join('%d:%d' % (Dp, len(allf[Dp])) for Dp in sorted(allf)),
          'total', sum(len(v) for v in allf.values()), 'INCONSISTENT %s' % bad if bad else 'consistent')
