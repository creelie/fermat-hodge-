#!/usr/bin/env python3
"""bypass_checks.py -- finite checks for Sect. VIII of the paper (run: python3 -I bypass_checks.py)

(1) Horn-rule closure.  The rule table of H8 tab:rules (code/closure_graph.py,
    transcribed by hand below, not imported) is extended by the facts of the
    literature that are PROVED for abelian varieties only:
      lef_B_ab   Lefschetz standard conjecture B for abelian varieties (Kleiman 1968)
      mot_ab     every Hodge class on an abelian variety is motivated
                 (Andre 1996; Milne arXiv:2010.08857v2 Remark 4)
      acc_ab     every Hodge class on an abelian variety is accessible
                 (Deligne 1982; Milne 2020 Theorem 3)
    and by the two abelian-scheme forms of (L) and (V) that Milne's Theorem 4 /
    Abdulali's Proposition 1 actually use:
      lef_B_absch   B for the total space of every abelian scheme over a smooth
                    complete curve (a NON-abelian variety)            -- open
      vhc_absch     (V) for flat classes in abelian schemes over smooth
                    complete curves                                   -- open
    with the rules  lef_B_absch => vhc_absch (Abdulali Prop. 1) and
    (vhc_absch, acc_ab) => HC_ab (Milne Thm 3 + Remark 3), and the converse
    HC_ab => vhc_absch (trivial).  Also prop:f2isab: red_weil => HC_ab.
    The script verifies: HC_ab is NOT derived from the proved/quoted base even
    with lef_B_ab and mot_ab adjoined (the abelian restriction of {L,M} is
    vacuous), and lists the minimal sufficient sets for HC_ab and for HC.

(2) Blow-up bookkeeping (Manin's formula): dim Hdg^p(Bl_Z X) - dim Alg^p(Bl_Z X)
    = [dim Hdg^p(X) - dim Alg^p(X)] + sum_{k=1}^{c-1} [dim Hdg^{p-k}(Z) - dim Alg^{p-k}(Z)],
    checked as an identity on symbolic ranks for the two residual carriers:
    Mumford square X x X (dim 8, two exceptional classes in H^4) blown up along
    a smooth centre Z, and a Weil 2n-fold.  This is only the additivity of the
    direct-sum decomposition; it records that the defect never decreases.
"""
from itertools import combinations

# ---- (1) rules of H8 tab:rules (premises, conclusion, label) -----------------
RULES = [
    (("HC_ab", "red_ab"), "HC", "ssec:closuremap"),
    (("red_ab",), "HC_ab", "prop:f3ishc"),
    (("HC_ab", "red_ab_mod"), "HC", "prop:f3prime"),
    (("weil_all", "red_weil"), "HC_ab", "ssec:closuremap"),
    (("weil_iq", "weil_cm"), "weil_all", "app:albert"),
    (("weil_triv", "weil_nontriv"), "weil_iq", "prop:separate"),
    (("base_point", "reduction", "orbit_dense", "P2_iq_s"), "weil_triv", "thm:semiregclosure"),
    (("base_point", "reduction", "orbit_dense", "P2_iq_ns"), "weil_nontriv", "thm:semiregclosure"),
    (("base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_s"), "weil_cm_triv", "thm:cmpropagation"),
    (("base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_ns"), "weil_cm_nontriv", "thm:cmpropagation"),
    (("weil_cm_triv", "weil_cm_nontriv"), "weil_cm", "prop:cmweil"),
    (("weil_triv",), "weil_nontriv", "prop:descent"),
    (("weil_cm_triv",), "weil_cm_nontriv", "prop:descent"),
    (("weil_cm_triv",), "weil_triv", "prop:descent"),
    (("lef_B", "mot"), "HC", "prop:lefmot"),
    (("lef_B", "mot_def"), "vhc", "prop:lefvhc"),
    (("vhc", "acc_ab"), "HC_ab", "thm:vhcab"),
    (("red_weil",), "HC_ab", "prop:f2isab"),
    # literature, abelian-scheme forms (Milne 2020 Sec. 5):
    (("lef_B_absch",), "vhc_absch", "Milne2020 Prop.1 (Abdulali 1994)"),
    (("vhc_absch", "acc_ab"), "HC_ab", "Milne2020 Thm 3 + Rem 3"),
    (("HC_ab",), "vhc_absch", "trivial"),
    (("lef_B",), "lef_B_absch", "restriction"),
    (("lef_B",), "lef_B_ab", "restriction"),
    (("vhc",), "vhc_absch", "restriction"),
    (("mot",), "mot_ab", "restriction"),
    (("HC",), "red_ab", "restriction"), (("HC",), "HC_ab", "restriction"),
    (("HC",), "red_weil", "restriction"), (("HC",), "red_ab_mod", "restriction"),
]
BASE = {"base_point", "reduction", "orbit_dense", "base_point_cm", "reduction_cm",
        "orbit_dense_cm", "mot_def", "acc_ab",
        "lef_B_ab", "mot_ab"}          # the two abelian-only literature facts
OPEN = ["red_ab", "red_ab_mod", "red_weil", "P2_iq_s", "P2_iq_ns", "P2_cm_s",
        "P2_cm_ns", "lef_B", "mot", "vhc", "lef_B_absch", "vhc_absch"]

def closure(seed):
    s = set(seed)
    while True:
        new = {c for p, c, _ in RULES if all(x in s for x in p)} - s
        if not new:
            return s
        s |= new

def minimal_sets(goal, leaves, maxsize=3):
    found = []
    for k in range(1, maxsize + 1):
        for S in combinations(leaves, k):
            if any(set(T) <= set(S) for T in found):
                continue
            if goal in closure(BASE | set(S)):
                found.append(S)
    return found

ok = True
cl = closure(BASE)
print("closure of proved/quoted + {lef_B_ab, mot_ab}:", sorted(cl))
for g in ("HC_ab", "HC", "vhc_absch", "lef_B_absch"):
    print("  %-12s derived: %s" % (g, g in cl))
    ok &= g not in cl
print("minimal sufficient sets for HC_ab:")
for S in minimal_sets("HC_ab", OPEN): print("   ", S)
print("minimal sufficient sets for HC:")
for S in minimal_sets("HC", OPEN): print("   ", S)
# equivalences
eq1 = "HC_ab" in closure(BASE | {"vhc_absch"}) and "vhc_absch" in closure(BASE | {"HC_ab"})
print("HC_ab <=> vhc_absch (given acc_ab):", eq1); ok &= eq1
eq2 = "HC_ab" in closure(BASE | {"lef_B_absch"})
print("lef_B_absch => HC_ab:", eq2); ok &= eq2
print("HC_ab => lef_B_absch:", "lef_B_absch" in closure(BASE | {"HC_ab"}), "(expected False)")

# ---- (2) blow-up bookkeeping ------------------------------------------------
def defect_blowup(defX, defZ, c, p):
    # defX[d], defZ[d]: dim Hdg^d - dim Alg^d for X and Z; codim c centre
    return defX.get(p, 0) + sum(defZ.get(p - k, 0) for k in range(1, c))
# Mumford square: two exceptional classes in H^4 (p=2) not known algebraic off CM points
defX = {2: 2}
for c in (2, 3, 4):
    for defZ in ({}, {1: 1}, {0: 0, 1: 2}):
        d = defect_blowup(defX, defZ, c, 2)
        assert d >= defX[2]
print("blow-up: defect of Bl_Z(X x X) in degree 4 is defect(X x X) + sum of defects of Z: never smaller  OK")
# Weil 2n-fold, Weil line of dimension 2 in degree 2n, n=2..5
for n in range(2, 6):
    for c in (2, 3):
        assert defect_blowup({n: 2}, {n - 1: 1}, c, n) >= 2
print("blow-up: Weil defect preserved for n=2..5  OK")
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
