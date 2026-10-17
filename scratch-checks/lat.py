"""F_2 images of Aoki's groups S_M and B_M.  Classes are vectors in F_2^(M-1)
(index y-1).  Provides basis of S-bar for membership tests."""
import sys
from math import gcd
import numpy as np


def primes_of(M):
    ps, n, p = [], M, 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ps.append(n)
    return ps


def standard(M):
    out = []
    for p in primes_of(M):
        if p >= M:
            continue
        d = M // p
        for i in range(1, d):
            if p == 2:
                s = [i, (i + M // 2) % M, (-2 * i) % M, M // 2]
            else:
                s = [(i + j * d) % M for j in range(p)] + [(-p * i) % M]
            if all(s):
                out.append(s)
    return out


def vec(ms, M):
    v = np.zeros(M - 1, dtype=np.uint8)
    for y in ms:
        v[y % M - 1] ^= 1
    return v


class F2Space:
    def __init__(self, n):
        self.n = n
        self.rows = {}  # pivot -> row

    def reduce(self, v):
        v = v.copy()
        while True:
            nz = np.flatnonzero(v)
            if len(nz) == 0:
                return v
            p = nz[0]
            if p in self.rows:
                v ^= self.rows[p]
            else:
                return v

    def add(self, v):
        r = self.reduce(v)
        nz = np.flatnonzero(r)
        if len(nz) == 0:
            return False
        self.rows[nz[0]] = r
        return True

    def contains(self, v):
        return not np.flatnonzero(self.reduce(v)).size


def Sbar(M):
    S = F2Space(M - 1)
    for y in range(1, M):
        S.add(vec([y, M - y], M))
    for s in standard(M):
        S.add(vec(s, M))
    return S


if __name__ == "__main__":
    M = int(sys.argv[1])
    S = Sbar(M)
    print(M, "rank S-bar", len(S.rows))
