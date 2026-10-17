# Canonical forms (lex-min over units of Z/(D'e')) of the residual
# configurations in R_v_w_e.txt files, grouped by D' (2,3-part of the lcm of
# the orders), with the sizes and the D at which each occurs.
import sys, math, re
from collections import defaultdict
def part23(n):
    d = 1
    for p in (2, 3):
        while n % p == 0: n //= p; d *= p
    return d
forms = defaultdict(set)
for fn in sys.argv[1:]:
    v, w, e = map(int, re.match(r'R_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]).groups())
    D = 2**v * 3**w; N = D * e
    for line in open(fn):
        if not line.startswith('   '): continue
        els = [tuple(map(int, t.split('/'))) for t in line.split()]
        L = 1
        for x, o in els: L = L * o // math.gcd(L, o)
        Dp = part23(L); Np = Dp * e; s = N // Np
        xs = [x // s for x, o in els]
        best = min(tuple(sorted(x * t % Np for x in xs)) for t in range(1, Np) if math.gcd(t, Np) == 1)
        forms[(e, Dp, best)].add(D)
for (e, Dp, b), Ds in sorted(forms.items()):
    Np = Dp * e
    print("e'=%d D'=%d level %d size %d: {%s}  orders %s  found at D in %s" % (e, Dp, Np, len(b), ', '.join(map(str, b)),
          ','.join(str(Np // math.gcd(x, Np)) for x in b), sorted(Ds)))
