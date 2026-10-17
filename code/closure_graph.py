#!/usr/bin/env python3
"""closure_graph.py -- the closure graph of Sect. III of the paper.

Eight statements: HC, F3, F2, F3p, L, M, V, AB.  Twelve rules, each one
theorem of the paper or of the literature (Table I).  The closure of a set
is the least set containing it and closed under the rules.  The script
computes the closure of all 256 subsets and lists the minimal subsets of
the seven hypotheses whose closure contains HC.  Expected: exactly six,
{F3}, {L,M}, {L,F3p}, {V,F3p}, {F2,F3p}, {AB,F3p}.
Run: python3 -I closure_graph.py
"""
from itertools import combinations

STMTS = ["HC", "F3", "F2", "F3p", "L", "M", "V", "AB"]
RULES = [(("HC",), "F3"), (("F3",), "HC"), (("HC",), "F2"), (("HC",), "F3p"),
         (("HC",), "AB"), (("F2",), "AB"), (("AB",), "F2"), (("AB", "F3p"), "HC"),
         (("L", "M"), "HC"), (("L",), "AB"), (("V",), "AB"), (("HC",), "M")]

def closure(s):
    s = set(s)
    while True:
        new = {c for prem, c in RULES if all(p in s for p in prem)} - s
        if not new:
            return frozenset(s)
        s |= new

def main():
    allsets = [frozenset(c) for r in range(9) for c in combinations(STMTS, r)]
    assert len(allsets) == 256
    derive = {s for s in allsets if "HC" in closure(s)}
    hyps = [x for x in STMTS if x != "HC"]
    cand = [frozenset(c) for r in range(8) for c in combinations(hyps, r)]
    minimal = [s for s in cand if s in derive and
               not any(t in derive for t in cand if t < s)]
    minimal.sort(key=lambda s: (len(s), sorted(s)))
    print("subsets:", len(allsets), " deriving HC:", len(derive))
    print("minimal sufficient sets:", len(minimal))
    for s in minimal:
        print("  {" + ",".join(sorted(s, key=STMTS.index)) + "}")
    expected = {frozenset(x) for x in [["F3"], ["L", "M"], ["L", "F3p"], ["V", "F3p"],
                                       ["F2", "F3p"], ["AB", "F3p"]]}
    ok = set(minimal) == expected
    ok &= all((s in derive) == ("HC" in s or any(e <= s for e in expected)) for s in allsets)
    for name, s in [("F2", ["F2"]), ("F3p", ["F3p"]), ("L", ["L"]), ("M", ["M"]), ("V", ["V"]),
                    ("AB", ["AB"]), ("L,V", ["L", "V"]), ("M,F3p", ["M", "F3p"])]:
        ok &= frozenset(s) not in derive
    print("closure_graph: " + ("PASS" if ok else "FAIL"))
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
