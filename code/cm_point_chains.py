"""Pieces outside every closed chain at the CM point A_0 = E_0^6 (Proposition VI.14 and
Corollary VI.15 of Bhattacharjee-Bhattacharya 2026, doi:10.5281/zenodo.23461752).

A convolution E of pieces F_a[s_a] has Hom^*(E, E) = sum of the blocks Ext^k(F_a, F_b) in total
degree k + s_b - s_a, with the twisted differential d y = sum m_{p+q+1}(delta, .., delta, y, delta, ..).
Let Gamma be the directed graph on the pieces with an edge u -> v (u != v) when
Ext^{1 + s_u - s_v}(F_u, F_v) != 0.  A term of d y landing in a diagonal block (a, a) runs along a
closed walk through a in Gamma, so when a threefold piece a lies on no cycle of Gamma the class
ev_{F_a}(v) survives in Ext^2(E, E) and the criterion fails (dim Ext^2 >= 58).

This program checks, with the Ext dimensions of cm_point_counts.py (Lemmas VI.8, VI.9; for two
threefolds meeting along a curve or a surface the E_2 page, an upper bound for the groups, hence an
upper bound for the edges of Gamma and a lower bound for the chain-free pieces):

  (A) the named configurations of Table III: the thirty-five pieces, family (a) with L^1[-2], L^2[-1],
      L^3[0], L^4[1], family (c) with Z_(1,1,1) L^1 at [-1], [0] and L^2 at [1], [2], family (d);
  (B) family (a) over its whole window: 2401 polarised configurations, no closed chain at all
      (Corollary VI.15 (i));
  (C) the sixteen pieces at the top shift are entered by no piece of positive twist at a shift at most
      one above them, for every zeta in mu_4^3, twists 1..4 and shifts -3..2, and by no base piece;
      a piece at shift 3 does enter them (Corollary VI.15 (ii) and its sharpness);
  (D) family (c) over an enlarged window: copies of Z_(1,1,1) L^k at two twists 1 <= k < k' <= 3, a
      pair at each twist with shifts in -3..3, L^1, L^2, L^3 at a common shift in -3..3: 3024
      configurations with the polarised shape, each with at least fifteen chain-free threefold
      pieces; the polarised shape holds exactly when both pairs have shifts of opposite parity;
  (E) line bundles of positive twist with the thirty-two at shifts 0, 1: for four or five line
      bundles with twists in 1..5 and shifts in -3..3, one of the two classes of sixteen pieces is
      entirely chain-free; with L^1[-2], ..., L^6[3] every piece lies on a cycle (Corollary VI.15 (iii)).

    python3 -I cm_point_chains.py
"""
from __future__ import annotations

import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cm_point_counts import (MU4, ONE, ZERO, ZETAS, Piece, base, ext_dims, fadd, polarised, zmeet,  # noqa: E402
                             zsign)

fails = 0


def check(name: str, ok: bool) -> None:
    global fails
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok:
        fails += 1


# -- cached Chern characters and the polarised test ------------------------------------------------------
_CH = {}


def piece_ch(p: Piece):
    key = (p.kind, p.zeta, p.twist, p.shift)
    if key not in _CH:
        _CH[key] = p.ch()
    return _CH[key]


def polarised_config(pieces) -> bool:
    ch = {}
    for p in pieces:
        ch = fadd(ch, piece_ch(p))
    ok, N, _ = polarised(ch)
    return ok and N != ZERO


# -- the graph Gamma -------------------------------------------------------------------------------------
_EXT = {}


def ext_nonzero_degrees(p: Piece, q: Piece):
    key = (p.kind, p.zeta, p.twist, q.kind, q.zeta, q.twist)
    if key not in _EXT:
        dims, _ = ext_dims(p, q)
        _EXT[key] = frozenset(k for k, v in dims.items() if v > 0)
    return _EXT[key]


def edge(p: Piece, q: Piece) -> bool:
    return (1 + p.shift - q.shift) in ext_nonzero_degrees(p, q)


_BASE_EDGES = {}


def edges(pieces):
    """Adjacency lists of Gamma; the edges among a leading run of base pieces are cached."""
    n = len(pieces)
    nb = 0
    while nb < n and pieces[nb].kind == "Z" and pieces[nb].twist == 0 and pieces[nb].shift in (0, 1) \
            and pieces[nb].zeta in ZETAS and pieces[nb].shift == (0 if zsign(pieces[nb].zeta) == 1 else 1):
        nb += 1
    key = tuple((p.zeta, p.shift) for p in pieces[:nb])
    if key not in _BASE_EDGES:
        _BASE_EDGES[key] = [[b for b in range(nb) if b != a and edge(pieces[a], pieces[b])] for a in range(nb)]
    E = [list(row) for row in _BASE_EDGES[key]] + [[] for _ in range(n - nb)]
    for a in range(n):
        pa = pieces[a]
        for b in (range(nb, n) if a < nb else range(n)):
            if b != a and edge(pa, pieces[b]):
                E[a].append(b)
    return E


def on_cycle(pieces) -> set:
    """The pieces lying on a cycle of Gamma: the vertices of the strongly connected components of size
    at least two (Tarjan)."""
    E = edges(pieces)
    n = len(pieces)
    index, low, stack, onstack, out = {}, {}, [], set(), set()
    counter = [0]
    sys.setrecursionlimit(10000)

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        onstack.add(v)
        for w in E[v]:
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                onstack.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) >= 2:
                out.update(comp)

    for v in range(n):
        if v not in index:
            strong(v)
    return out


def chain_free_threefolds(pieces):
    oc = on_cycle(pieces)
    return [a for a, p in enumerate(pieces) if p.kind == "Z" and a not in oc], oc


def Ls(spec):
    return [Piece("L", None, l, t) for l, t in spec]


def main() -> None:
    z111 = ZETAS[0]
    assert z111 == (ONE, ONE, ONE)
    B = base()
    top = [a for a, p in enumerate(B) if p.shift == 1]
    bottom = [a for a, p in enumerate(B) if p.shift == 0]
    check("thirty-two base pieces, sixteen at each shift", len(B) == 32 and len(top) == 16 and len(bottom) == 16)

    # (A) the named configurations
    base35 = B + Ls([(1, 0), (2, 0), (3, 0)])
    free, oc = chain_free_threefolds(base35)
    check("(A) thirty-five pieces: no closed chain (Proposition VI.11, Step 1)", len(oc) == 0 and len(free) == 32)
    famA = B + Ls([(1, -2), (2, -1), (3, 0), (4, 1)])
    free, oc = chain_free_threefolds(famA)
    check("(A) family (a) at L^1[-2], L^2[-1], L^3[0], L^4[1]: no closed chain", polarised_config(famA) and len(oc) == 0)
    famC = B + [Piece("Z", z111, 1, -1), Piece("Z", z111, 1, 0), Piece("Z", z111, 2, 1), Piece("Z", z111, 2, 2)] + Ls([(1, 0), (2, 0), (3, 0)])
    free, oc = chain_free_threefolds(famC)
    expected_on = {a for a, p in enumerate(famC) if p.kind == "Z" and p.twist > 0} \
        | {a for a in bottom if zmeet(B[a].zeta, z111)[0] >= 1} | {a for a, p in enumerate(famC) if p.kind == "L" and p.twist == 2}
    check("(A) family (c): twenty-two chain-free threefold pieces, the sixteen at shift 1 and the six at shift 0 "
          "disjoint from Z_(1,1,1); on cycles: the four extra copies, the ten pieces at shift 0 meeting Z_(1,1,1) "
          "and L^2[0]", polarised_config(famC) and len(free) == 22 and set(top) <= set(free) and oc == expected_on)
    partner = [z for z in ZETAS if zmeet(z111, z)[0] == 2][0]
    famD = B + [Piece("Z", partner, 0, 0), Piece("Z", partner, 0, 1)] + Ls([(1, 0), (2, 0), (3, 0)])
    free, oc = chain_free_threefolds(famD)
    check("(A) family (d): twenty-eight chain-free threefold pieces (the partner copies have twist 0 and are not "
          "covered by Corollary VI.15; the configuration is closed by Proposition VI.13 (ii))",
          polarised_config(famD) and len(free) == 28)

    # (B) family (a) over the window of Table III
    count = cycles = 0
    for ts in itertools.product(range(-3, 4), repeat=4):
        pcs = B + Ls(list(zip((1, 2, 3, 4), ts)))
        if not polarised_config(pcs):
            continue
        count += 1
        if on_cycle(pcs):
            cycles += 1
    check(f"(B) family (a), four line bundles L^1..L^4 at shifts -3..3: {count} polarised configurations, "
          f"{cycles} with a closed chain", count == 2401 and cycles == 0)

    # (C) nothing of positive twist at a shift at most one above the top enters a top piece
    entrants = list(B)
    for zeta in itertools.product(MU4, repeat=3):
        for k in range(1, 5):
            for s in range(-3, 3):
                entrants.append(Piece("Z", zeta, k, s))
    for l in range(1, 5):
        for t in range(-3, 3):
            entrants.append(Piece("L", None, l, t))
    bad = [(repr(u), repr(B[v])) for u in entrants for v in top if u is not B[v] and edge(u, B[v])]
    check(f"(C) no edge into a top piece from the base or from {len(entrants) - 32} pieces of positive twist at "
          f"shifts -3..2", not bad)
    sharp = all(edge(Piece("L", None, l, 3), B[v]) for l in range(1, 5) for v in top) and \
        all(edge(Piece("Z", z111, 1, 3), B[v]) for v in top)
    check("(C) pieces at shift 3 do enter the top pieces: L^l[3] and Z_(1,1,1) L^1[3]", sharp)

    # (D) family (c) over the enlarged window
    tot = bad_c = 0
    least = 99
    parity_ok = True
    for k1, k2 in itertools.combinations(range(1, 4), 2):
        for s1, s1b in itertools.combinations_with_replacement(range(-3, 4), 2):
            for s2, s2b in itertools.combinations_with_replacement(range(-3, 4), 2):
                extra = [Piece("Z", z111, k1, s1), Piece("Z", z111, k1, s1b), Piece("Z", z111, k2, s2), Piece("Z", z111, k2, s2b)]
                for t in range(-3, 4):
                    pcs = B + extra + Ls([(1, t), (2, t), (3, t)])
                    pol = polarised_config(pcs)
                    parity_ok &= (pol == ((s1 - s1b) % 2 == 1 and (s2 - s2b) % 2 == 1))
                    if not pol:
                        continue
                    tot += 1
                    free, _ = chain_free_threefolds(pcs)
                    least = min(least, len(free))
                    if not free:
                        bad_c += 1
    check(f"(D) family (c), two further twists 1 <= k < k' <= 3, pairs at shifts -3..3, L^1, L^2, L^3 at a common "
          f"shift -3..3: {tot} polarised configurations, least number of chain-free threefold pieces {least}, "
          f"{bad_c} without one", tot == 3024 and least == 15 and bad_c == 0)
    check("(D) the polarised shape holds exactly when both pairs have shifts of opposite parity", parity_ok)

    # (E) four or five line bundles of positive twist with the thirty-two at shifts 0, 1
    tot = bad_e = 0
    for nL in (4, 5):
        for ls in itertools.combinations(range(1, 6), nL):
            for ts in itertools.product(range(-3, 4), repeat=nL):
                pcs = B + Ls(list(zip(ls, ts)))
                tot += 1
                _, oc = chain_free_threefolds(pcs)
                top_free = not (oc & set(top))
                bottom_free = not (oc & set(bottom))
                if not (top_free or bottom_free):
                    bad_e += 1
                shifts = set(ts)
                if not top_free and not {-1, 0, 1, 2, 3} <= shifts:
                    bad_e += 1
                if not bottom_free and not {-2, -1, 0, 1, 2} <= shifts:
                    bad_e += 1
    check(f"(E) four or five line bundles, twists in 1..5, shifts in -3..3: {tot} configurations; in each one class "
          f"of sixteen pieces is chain-free, and a class on cycles has line bundles at its five shifts ({bad_e} "
          f"exceptions)", bad_e == 0)
    six = B + Ls([(1, -2), (2, -1), (3, 0), (4, 1), (5, 2), (6, 3)])
    free, oc = chain_free_threefolds(six)
    check("(E) six line bundles L^1[-2], ..., L^6[3]: every piece lies on a cycle", polarised_config(six) and not free and len(oc) == 38)

    print(f"cm_point_chains: {'PASS' if fails == 0 else 'FAIL'} ({fails} failed)")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
