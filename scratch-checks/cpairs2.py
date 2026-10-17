"""Threefold + curve joins at level M not in S-bar (+ known), alpha with empty
Fine interior.  usage: cpairs2.py file M [known]"""
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
        S.add(vec([(M // int(q)) * int(x) for x in ms.split(",")], M))
units = [t for t in range(1, M) if gcd(t, M) == 1]
orbs = [tuple(int(x) for x in line.split()[:5]) for line in open(fn)]
def typ(a, t):
    return sum((t * x) % M for x in a) // M
table = {}
for b0 in range(1, M):
    for b1 in range(b0, M):
        b2 = (-b0 - b1) % M
        if b2 == 0 or b2 < b1:
            continue
        b = (b0, b1, b2)
        key = tuple(4 - typ(b, t) for t in units)
        table.setdefault(key, []).append(b)
zc = {}; nc = 0; good = 0
for a in orbs:
    key = tuple(typ(a, t) for t in units)
    for b in table.get(key, []):
        if S.contains(vec(list(a) + list(b), M)):
            continue
        nc += 1
        if a not in zc:
            sh = shadow(a, M)
            zc[a] = (9.0, sh) if sh is not None else (value(a, M)[0], None)
        print("CAND", a, b, zc[a], flush=True)
        if zc[a][0] < 1 - 1e-9:
            good += 1
            print("GOOD", a, b, flush=True)
print("cands", nc, "tested", len(zc), "good", good)
