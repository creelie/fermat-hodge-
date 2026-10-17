"""Least length of a balanced multiset of nonzero residues mod M with an odd
number of entries in a set S (S given by a predicate), by integer programming.
usage: minlen.py M mode   mode = nuP:<p> or nuR"""
import sys
from math import gcd
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
M = int(sys.argv[1]); mode = sys.argv[2]
units = [t for t in range(1, M) if gcd(t, M) == 1 and 2 * t < M]
ys = list(range(1, M))
if mode.startswith("nuP"):
    p = int(mode.split(":")[1])
    S = [y for y in ys if M // gcd(y, M) == p]
else:
    S = [y for y in ys if y * y % M == 1]
# rows: for t in units: sum n_y (2*(t*y % M) - M) = 0
A = np.array([[2 * ((t * y) % M) - M for y in ys] for t in units], dtype=float)
nY = len(ys)
# variables n_y (nY) and k (one) with sum_{y in S} n_y - 2k = 1
row = np.zeros(nY + 1); 
for y in S: row[y - 1] = 1
row[nY] = -2
Aall = np.vstack([np.hstack([A, np.zeros((len(units), 1))]), row])
lo = np.concatenate([np.zeros(len(units)), [1]]); hi = lo.copy()
c = np.concatenate([np.ones(nY), [0]])
res = milp(c, constraints=LinearConstraint(Aall, lo, hi), integrality=np.ones(nY + 1),
           bounds=Bounds(np.zeros(nY + 1), np.concatenate([np.full(nY, 20), [100]])),
           options={"time_limit": 300})
if res.x is None:
    print(M, mode, "none", res.message); sys.exit()
n = np.round(res.x[:nY]).astype(int)
ms = [y for y in ys for _ in range(n[y - 1])]
print(M, mode, "length", len(ms), ms)
