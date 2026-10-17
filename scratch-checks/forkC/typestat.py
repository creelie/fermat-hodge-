# type multiset (2,3-part of the order) of each configuration in fm_* files
import sys, math, re
from collections import Counter
def p23(n):
    d = 1
    for p in (2, 3):
        while n % p == 0: n //= p; d *= p
    return d
for fn in sys.argv[1:]:
    cnt = Counter()
    for line in open(fn):
        tag = line.split()[0]
        els = line.split('|')[1].split()
        ts = tuple(sorted(p23(int(t.split('/')[1])) for t in els))
        L = 1
        for t in ts: L = L * t // math.gcd(L, t)
        cnt[(tag, L, ts)] += 1
    print(fn)
    for k, v in sorted(cnt.items()): print('   ', v, k)
