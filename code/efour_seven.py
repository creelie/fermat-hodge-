"""efour_seven.py -- the computation of Remark VI.39 (the ten remaining arrangements): convolutions of the
128 Weil line bundles L_zeta on E_0^8 whose shifts lie in seven consecutive integers.

Pieces zeta in {1,i,-1,-i}^4 with prod zeta = +-1; a ratio r = zeta'/zeta is written additively as
k in (Z/4)^4 with even sum, of the same parity iff sum k = 0 mod 4.  For a ratio moving the set J of
coordinates, dim H^k = D(r) * C(2(4-|J|), k-|J|) with D(r) = prod_{j in J} |1 - r_j|^2.

Part (A) recomputes exactly the per-piece weights of the families used and the largest absolute
value of a character sum over the characters nontrivial on the ratios of one parity.
Part (B), for every one of the twelve arrangements (even values containing 0 and 6, odd values a
single value or {1,5}) and every distribution of the 64 pieces of each parity over its values,
bounds dim Ext^2(E,E) below by the sum of three families of surviving groups (H^4 at spread two,
H^3 at adjacent shifts less their targets, H^5 at spread three less their sources), each bounded by
per-piece degrees, cut bounds and the expander mixing lemma, minimised by linear programming
(scipy, HiGHS, double precision).  It checks that every bound exceeds 104 for eleven of the twelve, and for
{0,1,2,4,5,6} that it fails on exactly 585753 of the 2501793 distributions, so that arrangement is open.
Usage: python3 efour_seven.py [processes] [arrangement ...], an arrangement written as 0,2,5,6.
About two hours on four cores for all twelve.  Requirements: numpy, scipy.
"""
import sys, itertools, cmath
from math import sqrt, comb
from itertools import product
from multiprocessing import Pool
import numpy as np
from scipy.optimize import linprog

G = [k for k in product(range(4), repeat=4) if sum(k) % 2 == 0]
G0 = [k for k in G if sum(k) % 4 == 0]
def moved(r): return [j for j in range(4) if r[j] != 0]
def Dw(r):
    v = 1
    for j in moved(r): v *= 4 if r[j] == 2 else 2
    return v
def dimH(r, k):
    m = len(moved(r))
    return 0 if k < m or k > 8 - m else Dw(r) * comb(2 * (4 - m), k - m)
def parity(r): return 0 if sum(r) % 4 == 0 else 1
def wl(deg, same): return {r: dimH(r, deg) for r in G if (parity(r) == 0) == same and r != (0, 0, 0, 0) and dimH(r, deg)}
FAM = {'w13': {r: Dw(r) for r in G0 if len(moved(r)) == 4 and 2 in r},
       'w28': {r: Dw(r) for r in G if parity(r) == 1 and len(moved(r)) == 3},
       'h5s': wl(5, True), 'h5c': wl(5, False), 'h6c': wl(6, False), 'h2c': wl(2, False), 'h3s': wl(3, True)}
def lam_of(w):
    best = 0.0
    for chi in product(range(4), repeat=4):
        if all(sum(a * b for a, b in zip(chi, r)) % 4 == 0 for r in G0): continue
        s = sum(v * cmath.exp(2j * cmath.pi * sum(a * b for a, b in zip(chi, r)) / 4) for r, v in w.items())
        best = max(best, abs(s))
    return best
PW = {k: sorted(w.values(), reverse=True) for k, w in FAM.items()}
DEG = {k: sum(v) for k, v in PW.items()}
LAM = {k: lam_of(w) for k, w in FAM.items()}
SAME = {'w13': True, 'w28': False, 'h5s': True, 'h5c': False, 'h6c': False, 'h2c': False, 'h3s': True}
def percap(key, n): return sum(PW[key][:n])
def cap(key, X, Y): return min(X*percap(key, Y), Y*percap(key, X))
def mixv(key, X, Y):
    d, lam = DEG[key], LAM[key]
    if SAME[key]: return d*X*Y/64, lam/64*sqrt(X*(64-X)*Y*(64-Y))
    return 2*d*X*Y/128, 2*lam/128*sqrt(X*(64-X)*Y*(64-Y))
def up(key, X, Y):
    m, e = mixv(key, X, Y); return min(cap(key, X, Y), m + e)
def lo(key, X, Y):
    m, e = mixv(key, X, Y); return max(0, m - e)

def lp(c, A_ub, b_ub, A_eq, b_eq, bounds):
    r = linprog(c, A_ub=A_ub if A_ub else None, b_ub=b_ub if b_ub else None,
                A_eq=A_eq if A_eq else None, b_eq=b_eq if b_eq else None, bounds=bounds, method='highs')
    if r.status != 0: raise RuntimeError(r.message)
    return r.fun

def f1_bound(levs, S):
    """min of sum_{|u-v|=2} w13(T_u,T_v) over the 13-weight relaxation for one parity."""
    if len(levs) < 2: return 0.0
    pairs = list(itertools.combinations(levs, 2)); n = len(pairs); pi = {p: i for i, p in enumerate(pairs)}
    c = np.zeros(n)
    for (u, v) in pairs:
        if abs(u - v) == 2: c[pi[(u, v)]] = 1
    A_ub, b_ub = [], []
    for u in levs:                                   # sum_{v != u} w_uv <= 1024 a_u
        row = np.zeros(n)
        for (a, b) in pairs:
            if u in (a, b): row[pi[(a, b)]] = 1
        A_ub.append(row); b_ub.append(1024*S[u])
    for r in range(1, len(levs)):                    # cuts >= 1024
        for J in itertools.combinations(levs, r):
            row = np.zeros(n)
            for (a, b) in pairs:
                if (a in J) != (b in J): row[pi[(a, b)]] = -1
            A_ub.append(row); b_ub.append(-1024)
    bounds = [(lo('w13', S[a], S[b]), up('w13', S[a], S[b])) for (a, b) in pairs]
    return lp(c, A_ub, b_ub, None, None, bounds)

def bip_lp(levs, S, objective):
    """joint relaxation of the 28-weights and the h5c-weights between A-levels and B-levels.
    objective: ('adj',) -> min sum over adjacent pairs of w28; ('h5c', u, v) -> min h5c(T_u,T_v)."""
    A = [v for v in levs if v % 2 == 0]; B = [v for v in levs if v % 2 == 1]
    pairs = [(u, v) for u in A for v in B]; n = len(pairs); pi = {p: i for i, p in enumerate(pairs)}
    N = 2*n                                           # w28 then h5c
    c = np.zeros(N)
    if objective[0] == 'adj':
        for (u, v) in pairs:
            if abs(u - v) == 1: c[pi[(u, v)]] = 1
    else:
        c[n + pi[(objective[1], objective[2])]] = 1
    A_eq, b_eq = [], []
    for u in A:
        for off, key in ((0, 'w28'), (n, 'h5c')):
            row = np.zeros(N)
            for (a, b) in pairs:
                if a == u: row[off + pi[(a, b)]] = 1
            A_eq.append(row); b_eq.append(DEG[key]*S[u])
    for v in B:
        for off, key in ((0, 'w28'), (n, 'h5c')):
            row = np.zeros(N)
            for (a, b) in pairs:
                if b == v: row[off + pi[(a, b)]] = 1
            A_eq.append(row); b_eq.append(DEG[key]*S[v])
    A_ub, b_ub = [], []
    for (a, b) in pairs:                              # h5c >= w28 on every pair
        row = np.zeros(N); row[pi[(a, b)]] = 1; row[n + pi[(a, b)]] = -1
        A_ub.append(row); b_ub.append(0)
    alll = sorted(levs)
    for r in range(1, len(alll)):                     # cuts of (Gamma, S28) >= 640
        for J in itertools.combinations(alll, r):
            row = np.zeros(N)
            for (a, b) in pairs:
                if (a in J) != (b in J): row[pi[(a, b)]] = -1
            if row.any(): A_ub.append(row); b_ub.append(-640)
    bounds = [(lo('w28', S[a], S[b]), up('w28', S[a], S[b])) for (a, b) in pairs] + \
             [(lo('h5c', S[a], S[b]), up('h5c', S[a], S[b])) for (a, b) in pairs]
    return lp(c, A_ub, b_ub, A_eq, b_eq, bounds)

def tgt_upper(levs, S, tg):
    """max of the sum of the target groups under per-level degree limits (small LP, maximise)."""
    if not tg: return 0.0
    tg = sorted(tg); n = len(tg); c = -np.ones(n)
    A_ub, b_ub = [], []
    for key in ('h5s', 'h6c'):
        for u in levs:
            row = np.zeros(n)
            for i, (k, a, b) in enumerate(tg):
                if k == key and u in (a, b): row[i] = 1
            if row.any(): A_ub.append(row); b_ub.append(DEG[key]*S[u])
    bounds = [(0, up(k, S[a], S[b])) for (k, a, b) in tg]
    return -lp(c, A_ub, b_ub, None, None, bounds)

def bound(levels, S, detail=False):
    occ = set(levels)
    A = [v for v in levels if v % 2 == 0]; B = [v for v in levels if v % 2 == 1]
    parts = {}
    parts['F1'] = f1_bound(A, S) + f1_bound(B, S)
    adj = [(v, v-1) for v in levels if v-1 in occ]
    k3 = 0.0
    if adj:
        src = bip_lp(levels, S, ('adj',))
        tg = set()
        for v, _ in adj:
            for c in (v+1, v):
                if c in occ and c-2 in occ: tg.add(('h5s', c, c-2))
            for c in (v+2, v, v+1):
                if c in occ and c-3 in occ: tg.add(('h6c', c, c-3))
        k3 = src - tgt_upper(levels, S, tg)
    parts['F3'] = max(0.0, k3)
    f2 = 0.0
    for v in levels:
        if v-3 in occ:
            u, w = (v, v-3) if v % 2 == 0 else (v-3, v)         # (A-level, B-level) order for the LP
            grp = bip_lp(levels, S, ('h5c', u, w))
            srcs = 8*sum(S.get(x, 0) for x in (v, v-1, v-2, v-3))
            for (a, b, key) in ((v, v-1, 'h2c'), (v-1, v-2, 'h2c'), (v-2, v-3, 'h2c'), (v, v-2, 'h3s'), (v-1, v-3, 'h3s')):
                if a in occ and b in occ: srcs += up(key, S[a], S[b])
            f2 += max(0.0, grp - srcs)
    parts['F2'] = f2
    tot = sum(parts.values())
    return (tot, parts) if detail else tot

def compositions(n, k):
    if k == 1: yield (n,); return
    for i in range(1, n - k + 2):
        for rest in compositions(n - i, k - 1): yield (i,) + rest

def scan(levels, step=None, limit=104):
    A = [v for v in levels if v % 2 == 0]; B = [v for v in levels if v % 2 == 1]
    worst = (10**9, None); nfail = 0; count = 0
    for ca in compositions(64, len(A)):
        if step and any(c % step for c in ca): continue
        for cb in compositions(64, len(B)):
            if step and any(c % step for c in cb): continue
            S = dict(zip(A, ca)); S.update(zip(B, cb)); count += 1
            b = bound(levels, S)
            if b <= limit: nfail += 1
            if b < worst[0]: worst = (b, dict(S))
    return worst, nfail, count


LIMIT = 104
def work(args):
    levels, ca = args
    A = [v for v in levels if v % 2 == 0]; B = [v for v in levels if v % 2 == 1]
    SA = dict(zip(A, ca)); fa = f1_bound(A, SA)
    CB = list(compositions(64, len(B)))
    if fa > LIMIT: return (fa, 0, len(CB))
    worst, nfail = 10**9, 0
    for cb in CB:
        S = dict(SA); S.update(zip(B, cb)); b = bound(levels, S)
        nfail += b <= LIMIT; worst = min(worst, b)
    return (worst, nfail, len(CB))

ARRANGEMENTS = [sorted(set(e) | set(o)) for e in ((0, 2, 6), (0, 4, 6), (0, 2, 4, 6)) for o in ((1,), (3,), (5,), (1, 5))]
# The bound decides eleven of the twelve; for the even values {0,2,4,6} with the odd values {1,5}
# it vanishes on some distributions (least 0.0 at (2,5,5,52), (52,12)), and the arrangement is open.
UNDECIDED = {(0, 1, 2, 4, 5, 6): (585753, 2501793)}

if __name__ == "__main__":
    fails = 0
    exp = {'w13': (1024, 640), 'w28': (640, 256), 'h5s': (960, 384), 'h5c': (1072, 496), 'h6c': (144, 96), 'h2c': (144, 96), 'h3s': (960, 384)}
    for k, (d, l) in exp.items():
        ok = DEG[k] == d and abs(LAM[k] - l) < 1e-6
        fails += not ok
        print(f"(A) {k}: {len(FAM[k])} ratios, degree {DEG[k]}, largest nontrivial |eigenvalue| {LAM[k]:.6f}", "PASS" if ok else "FAIL", flush=True)
    procs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    arrs = [[int(x) for x in a.split(',')] for a in sys.argv[2:]] or ARRANGEMENTS
    with Pool(procs) as pool:
        for levels in arrs:
            A = [v for v in levels if v % 2 == 0]
            res = pool.map(work, [(levels, ca) for ca in compositions(64, len(A))], chunksize=50)
            least = min(r[0] for r in res); nf = sum(r[1] for r in res); tot = sum(r[2] for r in res)
            want = UNDECIDED.get(tuple(levels), (0, tot))
            ok = (nf, tot) == want if tuple(levels) in UNDECIDED else nf == 0
            fails += not ok
            tag = "UNDECIDED (as expected)" if tuple(levels) in UNDECIDED and ok else ("PASS" if ok else "FAIL")
            print(f"(B) shifts {levels}: {tot} distributions, least bound {least:.1f}, failing {nf}", tag, flush=True)
    print("efour_seven: PASS" if fails == 0 else f"efour_seven: {fails} FAILED")
    sys.exit(1 if fails else 0)
