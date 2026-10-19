"""Line bundles in any number at the CM point A_0 = E_0^6 (Theorem VI.23 and Remark VI.25 of
Bhattacharjee-Bhattacharya 2026, doi:10.5281/zenodo.23461752).

A convolution E of pieces O_{Z_x} L^{k_x}[s_x] (pairwise distinct threefolds Z_x) and L^{l_i}[t_i]
(pairwise distinct exponents) meets the polarised criterion only if, for the v in T D_h with
ev_T(v) != 0 at a threefold piece T, the class ev_E(v) is a coboundary D(eta).  The diagonal
component D(eta)_{TT} is a sum over the directed cycles of Gamma through T that have exactly one
edge on which the twisting cochain delta vanishes (Lemma VI.18, Proposition VI.19), so every threefold piece lies on
such an effective cycle, of both parities of shift (Lemma VI.21).  Between two line bundles two
shifts apart, the component (a, c) of the Maurer-Cartan equation is the sum over the paths of
Gamma from a to c on which delta vanishes nowhere; when a -> b -> c is the only such path it gives
delta_ab delta_bc = 0, impossible for two nonzero sections on the integral A_0 (rule E2, Lemma VI.20(i)); and when
a -> b -> c is the only path of Gamma at all and delta_bc = 0 != delta_ab, the component (a, c) of
D(eta) = ev_E(v) gives eta_bc = 0, so a cycle whose zero edge is b -> c carries nothing (rule E3, Lemma VI.20(ii)).

A configuration is a tuple of shifts of n line bundles, the i-th entry being the shift of the
line bundle of i-th smallest exponent; only the order of the exponents and the shifts matter.
The edges of Gamma between line bundles are

  up    L^l[s] -> L^l'[s+1], l' > l           (Hom, degree 0)
  down  L^l[s] -> L^l'[s-5], l' < l           (Ext^6)
  run   L^l[s] -> threefold pieces -> L^l'[s-b], b >= 1, the degrees of Lemmas VI.8 and VI.9.

The run table is computed symbolically from the comparisons that decide the degrees (twist of a
threefold against the entry and exit exponents and against its neighbours, dimension of the
intersection of two threefolds), so every realisable run is admitted, and every run and every down
edge is taken to carry a nonzero component of delta.  Both choices enlarge the set of effective
cycles and the set of paths, so the classification below is a superset check: a configuration
classified 'none' carries no effective cycle through a threefold piece for any delta, and one
classified 'one' carries effective cycles through threefold pieces of one parity of shift only.

    python3 -I line_bundle_chains.py [NMAX]      (NMAX = 8 by default; the whole run takes about half a minute on four cores)
"""
from __future__ import annotations

import itertools
import sys
from functools import lru_cache
from multiprocessing import Pool

BMAX = 12          # largest excess of a run that can matter: a cycle with n <= 8 line bundles has u <= 7

EXPECTED = {       # n: (configurations, both parities, one parity, none)
    4: (75, 0, 0, 75),
    5: (541, 0, 0, 541),
    6: (4683, 0, 4, 4679),
    7: (47293, 0, 140, 47153),
    8: (545835, 31, 3235, 542569),
}


# ---------------------------------------------------------------- the degrees of Lemmas VI.8, VI.9

def enter_degrees(rel_k_l):
    """Ext^*(L^l, O_Z L^k): k > l degree 0; k < l degree 3; k = l degrees 0..3."""
    return {">": (0,), "<": (3,), "=": (0, 1, 2, 3)}[rel_k_l]


def leave_degrees(rel_k_l):
    """Ext^*(O_Z L^k, L^l): l > k degree 3; l < k degree 6; l = k degrees 3..6."""
    return {"<": (3,), ">": (6,), "=": (3, 4, 5, 6)}[rel_k_l]


def internal_degrees(direction):
    """Ext^*(O_Z L^k, O_Z' L^k') for Z != Z' meeting in dimension d: degrees 3-d..3 (k' > k),
    3..3+d (k' < k), 3-d..3+d (k' = k); degree 0 never, degree 1 only at equal shifts, excluded."""
    return {"up": (2, 3), "eq": (2, 3, 4, 5), "down": (3, 4, 5)}[direction]


def run_table():
    """RUNS[(b, dec)]: the excesses x accumulated before a threefold piece, over all runs of total
    excess b from L^l to L^l' with l' < l (dec) or l' > l (not dec).  A state is the relation of the
    current twist to l'."""
    table = {}
    for dec in (False, True):
        # relation of k_1 to l' from the relation of k_1 to l
        if dec:
            first = {">": (">",), "=": (">",), "<": ("<", "=", ">")}
        else:
            first = {">": ("<", "=", ">"), "=": ("<",), "<": ("<",)}
        step = {("<", "up"): ("<", "=", ">"), ("=", "up"): (">",), (">", "up"): (">",),
                ("<", "eq"): ("<",), ("=", "eq"): ("=",), (">", "eq"): (">",),
                ("<", "down"): ("<",), ("=", "down"): ("<",), (">", "down"): ("<", "=", ">")}

        @lru_cache(maxsize=None)
        def finish(rel, x):
            """total excesses reachable from a threefold at accumulated excess x, relation rel to l'"""
            tot = {x + d - 1 for d in leave_degrees(rel)}
            if x < BMAX:
                for direction in ("up", "eq", "down"):
                    for d in internal_degrees(direction):
                        if x + d - 1 <= BMAX:
                            for rel2 in step[(rel, direction)]:
                                tot |= finish(rel2, x + d - 1)
            return frozenset(t for t in tot if t <= BMAX)

        seen = set()
        stack = []
        for rel_l in ("<", "=", ">"):
            for d in enter_degrees(rel_l):
                for rel in first[rel_l]:
                    st = (rel, d - 1)
                    if st not in seen:
                        seen.add(st)
                        stack.append(st)
        while stack:
            rel, x = stack.pop()
            if x >= BMAX:
                continue
            for direction in ("up", "eq", "down"):
                for d in internal_degrees(direction):
                    for rel2 in step[(rel, direction)]:
                        st = (rel2, x + d - 1)
                        if st[1] <= BMAX and st not in seen:
                            seen.add(st)
                            stack.append(st)
        for b in range(1, BMAX + 1):
            table[(b, dec)] = frozenset(x for (rel, x) in seen if b in finish(rel, x))
    return table


RUNS = run_table()


# ---------------------------------------------------------------- the graph on a configuration

def graph(conf):
    """Adjacency of the abstract graph: (target, kind, data); data is the up-edge index for 'up'
    and the set of parities of threefold shifts for 'run'."""
    n = len(conf)
    s = conf
    up = [(a, b) for a in range(n) for b in range(a + 1, n) if s[b] == s[a] + 1]
    upi = {e: i for i, e in enumerate(up)}
    adj = [[] for _ in range(n)]
    for (a, b) in up:
        adj[a].append((b, "up", upi[(a, b)]))
    for a in range(n):
        for b in range(n):
            if b == a:
                continue
            beta = s[a] - s[b]
            if beta >= 1:
                xs = RUNS.get((beta, b < a), frozenset())
                if xs:
                    adj[a].append((b, "run", frozenset((s[a] - x) % 2 for x in xs)))
            if b < a and s[b] == s[a] - 5:
                adj[a].append((b, "down", None))
    return up, adj


def paths(adj, a, c):
    """All paths a -> c through distinct line bundles, as tuples of (kind, up-edge index or None)."""
    out = []
    stack = [(a, frozenset([a]), ())]
    while stack:
        v, vis, steps = stack.pop()
        for (w, kind, data) in adj[v]:
            if w in vis:
                continue
            st = steps + ((kind, data if kind == "up" else None),)
            if w == c:
                out.append(st)
                continue
            stack.append((w, vis | {w}, st))
    return out


def cycles(adj, n):
    """Directed cycles through at least one run, as (set of up-edge indices, parities)."""
    out = []
    for start in range(n):
        stack = [(start, (start,), frozenset(), frozenset(), False)]
        while stack:
            v, path, ups, par, hasrun = stack.pop()
            for (w, kind, data) in adj[v]:
                nups, npar, nrun = ups, par, hasrun
                if kind == "up":
                    nups = ups | {data}
                elif kind == "run":
                    npar = par | data
                    nrun = True
                if w == start:
                    if nrun:
                        out.append((nups, npar))
                    continue
                if w < start or w in path:
                    continue
                stack.append((w, path + (w,), nups, npar, nrun))
    return out


def classify(conf):
    """'both', 'one' or 'none': the parities of shift of the threefold pieces on live cycles, over
    every set Z0 of up edges with delta = 0 admitted by rule E2, after rule E3."""
    n = len(conf)
    s = conf
    up, adj = graph(conf)
    cyc = cycles(adj, n)
    if not cyc:
        return "none"
    # pairs (a, c) two shifts apart with l_a < l_c: all their paths, as sets of up-edge indices
    # (None for a run or a down edge, which is taken to carry a nonzero delta)
    pairs = []
    for a in range(n):
        for c in range(a + 1, n):
            if s[c] != s[a] + 2:
                continue
            ps = [tuple(d for (k, d) in p) for p in paths(adj, a, c)]
            pairs.append(ps)
    # those whose only path in Gamma is a -> b -> c (two up edges), for rule E3
    single = [p[0] for p in pairs if len(p) == 1 and len(p[0]) == 2 and None not in p[0]]
    best = set()
    for r in range(len(up) + 1):
        for z in itertools.combinations(range(len(up)), r):
            z0 = frozenset(z)
            bad = False
            for ps in pairs:                                    # rule E2
                alive = [p for p in ps if not any(d in z0 for d in p if d is not None)]
                if len(alive) == 1 and len(alive[0]) == 2 and None not in alive[0]:
                    bad = True
                    break
            if bad:
                continue
            dead = {e2 for (e1, e2) in single if e2 in z0 and e1 not in z0} | \
                   {e1 for (e1, e2) in single if e1 in z0 and e2 not in z0}     # rule E3
            reach = set()
            for (ups, par) in cyc:
                zs = ups & z0
                if len(zs) <= 1 and not (zs & dead):
                    reach |= par
            if len(reach) == 2:
                return "both"                                   # for this one delta
            best |= reach
    return "one" if best else "none"


def contiguous(n):
    """Configurations whose set of shifts is an interval {0, ..., k-1} (Lemma VI.24)."""
    for k in range(1, n + 1):
        for conf in itertools.product(range(k), repeat=n):
            if len(set(conf)) == k:
                yield conf


def worker(confs):
    out = {"both": [], "one": 0, "none": 0}
    for conf in confs:
        c = classify(conf)
        if c == "both":
            out["both"].append(conf)
        else:
            out[c] += 1
    return out


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    fails = 0
    for b in range(1, 8):
        print(f"run excess {b}: threefolds at excess {sorted(RUNS[(b, False)])} (exit above), "
              f"{sorted(RUNS[(b, True)])} (exit below)")
    for n in range(4, nmax + 1):
        confs = list(contiguous(n))
        chunks = [confs[i::64] for i in range(64)]
        res = {"both": [], "one": 0, "none": 0}
        with Pool(4) as pool:
            for out in pool.imap_unordered(worker, chunks):
                res["both"] += out["both"]
                res["one"] += out["one"]
                res["none"] += out["none"]
        got = (len(confs), len(res["both"]), res["one"], res["none"])
        ok = got == EXPECTED[n]
        fails += 0 if ok else 1
        print(f"{'PASS' if ok else 'FAIL'}  {n} line bundles: {got[0]} configurations, "
              f"{got[1]} carry both parities, {got[2]} one, {got[3]} none"
              + ("" if ok else f"  (expected {EXPECTED[n]})"))
        for conf in sorted(res["both"]):
            print("      both:", conf)
    print(f"line_bundle_chains: {'PASS' if fails == 0 else 'FAIL'} ({fails} failed)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
