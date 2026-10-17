"""Joins of a level-one threefold character alpha and a curve character b at
level M with <t alpha> + <t b> = 4 for all units t and an odd number of
entries of order L; alpha with empty Fine interior.
usage: python3 cpairs.py file M L"""
import sys
from math import gcd
sys.path.insert(0, "/dev/shm/hc")
from fine import value, shadow
fn, M, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
units = [t for t in range(1, M) if gcd(t, M) == 1]
orbs = []
for line in open(fn):
    f = line.split()
    orbs.append((tuple(int(x) for x in f[:5]), int(f[5])))
def typ(a, t):
    return sum((t * x) % M for x in a) // M
def order(x):
    return M // gcd(x, M)
# curve characters b = (b0,b1,b2), all, sorted
table = {}
for b0 in range(1, M):
    for b1 in range(b0, M):
        b2 = (-b0 - b1) % M
        if b2 == 0 or b2 < b1:
            continue
        b = (b0, b1, b2)
        key = tuple(4 - typ(b, t) for t in units)
        nl = sum(1 for x in b if order(x) == L)
        table.setdefault(key, []).append((b, nl))
good = []
zc = {}
ncand = 0
for a, nl in orbs:
    key = tuple(typ(a, t) for t in units)
    for b, nb in table.get(key, []):
        if (nl + nb) % 2 == 0:
            continue
        ncand += 1
        if a not in zc:
            sh = shadow(a, M)
            zc[a] = (9.0, sh) if sh is not None else (value(a, M)[0], None)
        if zc[a][0] < 1 - 1e-9:
            good.append((a, b))
            print("GOOD", a, b, round(zc[a][0], 4), flush=True)
print("cands", ncand, "tested", len(zc), "shadow", sum(1 for v in zc.values() if v[1]), "good", len(good))
