"""Complementary pairs of level-one threefold characters at level M whose join
is not in S-bar + span(known), with empty Fine interiors.
usage: pairs2.py file M [known multisets as 'q:a,b,c;q:...']"""
import sys
from math import gcd
sys.path.insert(0, "/dev/shm/hc")
from fine import value, shadow
from lat import Sbar, vec
fn, M = sys.argv[1], int(sys.argv[2])
S = Sbar(M)
if len(sys.argv) > 3 and sys.argv[3]:
    for part in sys.argv[3].split(";"):
        q, ms = part.split(":")
        q = int(q)
        S.add(vec([(M // q) * int(x) for x in ms.split(",")], M))
units = [t for t in range(1, M) if gcd(t, M) == 1]
orbs = [tuple(int(x) for x in line.split()[:5]) for line in open(fn)]
def typ(a, t):
    return sum((t * x) % M for x in a) // M
tau = [{t: typ(a, t) for t in units} for a in orbs]
table = {}
for j, b in enumerate(orbs):
    for s in units:
        key = tuple(tau[j][(s * t) % M] for t in units)
        table.setdefault(key, []).append((j, s))
zc = {}
def z(i):
    if i not in zc:
        a = orbs[i]
        sh = shadow(a, M)
        zc[i] = (9.0, sh) if sh is not None else (value(a, M)[0], None)
    return zc[i]
ncand = 0; good = 0
for i, a in enumerate(orbs):
    key = tuple(tau[i][(-t) % M] for t in units)
    for j, s in table.get(key, []):
        if j < i:
            continue
        b = tuple(sorted((s * x) % M for x in orbs[j]))
        if S.contains(vec(list(a) + list(b), M)):
            continue
        ncand += 1
        zi = z(i)
        zj = z(j)
        print("CAND", a, b, zi, zj, flush=True)
        if zi[0] < 1 - 1e-9 and zj[0] < 1 - 1e-9:
            good += 1
            print("GOOD", a, b, flush=True)
print("cands", ncand, "tested", len(zc), "shadow", sum(1 for v in zc.values() if v[1]), "good", good)
