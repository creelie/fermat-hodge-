"""Complementary pairs of level-one threefold characters at level M whose join
has an odd number of entries of order L, and whose Fine interiors are empty.
usage: python3 pairs.py file M [limit]
"""
import sys
from math import gcd
sys.path.insert(0, "/dev/shm/hc")
from fine import value, shadow

fn, M = sys.argv[1], int(sys.argv[2])
limit = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
units = [t for t in range(1, M) if gcd(t, M) == 1]
orbs = []
for line in open(fn):
    f = line.split()
    a = tuple(int(x) for x in f[:5])
    nl = int(f[5])
    orbs.append((a, nl))


def typ(a, t):
    return sum((t * x) % M for x in a) // M


tau = [{t: typ(a, t) for t in units} for a, _ in orbs]
table = {}
for j, (b, nl) in enumerate(orbs):
    for s in units:
        key = tuple(tau[j][(s * t) % M] for t in units)
        table.setdefault(key, []).append((j, s))
cands = []
for i, (a, nl) in enumerate(orbs):
    key = tuple(tau[i][(-t) % M] for t in units)
    for j, s in table.get(key, []):
        if j < i:
            continue
        if (nl + orbs[j][1]) % 2 == 1:
            cands.append((i, j, s))
print("candidate pairs", len(cands))
zc = {}


def z(i):
    if i not in zc:
        a = orbs[i][0]
        sh = shadow(a, M)
        if sh is not None:
            zc[i] = (9.0, sh)
        else:
            zc[i] = (value(a, M)[0], None)
    return zc[i]


good = []
for n, (i, j, s) in enumerate(cands[:limit]):
    zi = z(i)
    if zi[0] >= 1 - 1e-9:
        continue
    zj = z(j)
    if zj[0] >= 1 - 1e-9:
        continue
    b = tuple(sorted((s * x) % M for x in orbs[j][0]))
    good.append((max(zi[0], zj[0]), orbs[i][0], b))
    print("GOOD", orbs[i][0], b, round(zi[0], 4), round(zj[0], 4), flush=True)
nsh = sum(1 for v in zc.values() if v[1] is not None)
print("tested orbits", len(zc), "with shadow", nsh, "good pairs", len(good))
