"""Fine interior of the simplex P_alpha for a character alpha of X^3_M.

value(a, M) returns (z, y, cols, weights): z = max over y in the simplex of
min over normalized dual vectors g of y.g.  F(P) is empty iff z < 1.
cols/weights is the support of the dual LP solution (a block pattern up to
scaling) when z < 1.
"""
import heapq
from math import gcd
import numpy as np
from scipy.optimize import linprog


def separate(y, a, M):
    """min over g >= 0, some g_k0 = 0, g != 0, g.a = 0 mod M, of y.g."""
    best = (float("inf"), None)
    n = len(a)
    for k0 in range(n):
        ks = [k for k in range(n) if k != k0]
        # Dijkstra from 0; we want shortest nonempty walk 0 -> 0
        dist = [float("inf")] * M
        prev = [None] * M
        # start with one step
        pq = []
        for k in ks:
            r = a[k] % M
            if y[k] < dist[r]:
                dist[r] = y[k]
                prev[r] = (None, k)
                heapq.heappush(pq, (y[k], r))
        done = [False] * M
        while pq:
            d, r = heapq.heappop(pq)
            if done[r] or d > dist[r]:
                continue
            done[r] = True
            if r == 0:
                break
            for k in ks:
                r2 = (r + a[k]) % M
                nd = d + y[k]
                if nd < dist[r2] - 1e-15:
                    dist[r2] = nd
                    prev[r2] = (r, k)
                    heapq.heappush(pq, (nd, r2))
        if dist[0] < best[0]:
            g = [0] * n
            r = 0
            steps = 0
            while True:
                pr, k = prev[r]
                g[k] += 1
                steps += 1
                if pr is None:
                    break
                r = pr
            best = (dist[0], tuple(g))
    return best


def value(a, M, maxit=500):
    n = len(a)
    cols = []
    for k in range(n):
        s = M // gcd(M, a[k])
        e = [0] * n
        e[k] = s
        cols.append(tuple(e))
    for it in range(maxit):
        # variables y_0..y_{n-1}, z ; maximize z
        A = []
        b = []
        for g in cols:
            A.append([-gk for gk in g] + [1.0])
            b.append(0.0)
        res = linprog(c=[0] * n + [-1.0], A_ub=A, b_ub=b,
                      A_eq=[[1.0] * n + [0.0]], b_eq=[1.0],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        y = res.x[:n]
        z = res.x[n]
        sv, g = separate(y, a, M)
        if sv >= z - 1e-9:
            duals = -np.array(res.ineqlin.marginals)
            supp = [(cols[i], duals[i]) for i in range(len(cols)) if duals[i] > 1e-9]
            return z, y, supp
        if g in cols:
            duals = -np.array(res.ineqlin.marginals)
            supp = [(cols[i], duals[i]) for i in range(len(cols)) if duals[i] > 1e-9]
            return z, y, supp
        cols.append(g)
    raise RuntimeError("no convergence")


def shadow(a, M):
    for t in range(1, M):
        if gcd(t, M) == 1:
            continue
        v = [(t * x) % M for x in a]
        if all(v) and sum(v) == M:
            return t
    return None


if __name__ == "__main__":
    for a, M in [((51, 21, 86, 14, 56), 114), ((1, 25, 43, 57, 102), 114), ((1, 5, 8, 33, 41), 44),
                 ((1, 34, 44, 56, 69), 102), ((5, 35, 51, 96, 17), 102), ((1, 16, 26, 31, 36), 55)]:
        z, y, supp = value(a, M)
        print(M, a, round(z, 6), shadow(a, M), [(c, round(w, 4)) for c, w in supp])
