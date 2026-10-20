#!/usr/bin/env bash
# run_all.sh -- run every machine check of the archive and print one line per
# program.  Requirements: python3 with sympy, numpy and mpmath; julia; a C and
# a C++ compiler; lean (elan) for the certificate.  Set JULIA, CC, CXX or LEAN
# to override the commands.  Exit status 0 when every check passed.
set -u
cd "$(dirname "$0")"
JULIA=${JULIA:-julia}; CC=${CC:-cc}; CXX=${CXX:-c++}; LEAN=${LEAN:-lean}
fail=0
run() { # name, command...
  local name=$1; shift
  if "$@" > "/tmp/run_all_$name.log" 2>&1; then echo "PASS  $name"; else echo "FAIL  $name  (see /tmp/run_all_$name.log)"; fail=1; fi
}
run closure_graph.py   python3 -I closure_graph.py
run sqrt6_chain.py     python3 -I sqrt6_chain.py
run fricke_families.py python3 -I fricke_families.py
run product_object.py  python3 -I product_object.py
run convolution_checks.py python3 -I convolution_checks.py
run sixfold_link.py    python3 -I sixfold_link.py
run link_weights.py    python3 -I link_weights.py
run bypass_checks.py   python3 -I bypass_checks.py
run zeta9_invariants.py python3 -I zeta9_invariants.py
run zeta7_invariants.py python3 -I zeta7_invariants.py
run annihilator_exact.py python3 -I annihilator_exact.py
run riemann_roch_pieces.py python3 -I riemann_roch_pieces.py
run cm_point_ext.py    python3 -I cm_point_ext.py
run cm_point_counts.py python3 -I cm_point_counts.py
run cm_point_chains.py python3 -I cm_point_chains.py
run line_bundle_chains.py python3 -I line_bundle_chains.py
run threefold_supports.py python3 -I threefold_supports.py
run kummer_type.py     python3 -I kummer_type.py
run closure_graph.jl   "$JULIA" closure_graph.jl
run eigencharacter.jl  "$JULIA" eigencharacter.jl
tmp=$(mktemp -d)
run closure_graph.c    sh -c "$CC -O2 -o $tmp/cg closure_graph.c && $tmp/cg"
run closure_graph.cpp  sh -c "$CXX -std=c++17 -O2 -o $tmp/cgpp closure_graph.cpp && $tmp/cgpp"
run hilbert.c          sh -c "$CC -O2 -o $tmp/hilbert hilbert.c && $tmp/hilbert"
rm -rf "$tmp"
# the Lean certificate: 59 theorems, each axiom-free, on propext and Quot.sound, or on propext alone
run lean               sh -c "cd ../lean && $LEAN HodgeClosure.lean > /tmp/run_all_lean.out && test \$(grep -c 'does not depend on any axioms' /tmp/run_all_lean.out) -eq 49 && test \$(grep -c 'depends on axioms: \[propext, Quot.sound\]' /tmp/run_all_lean.out) -eq 2 && test \$(grep -c 'depends on axioms: \[propext\]' /tmp/run_all_lean.out) -eq 8"
# the sqrt6, Fricke and Kummer scripts report their own counts; they must read 25, 41 and 15
grep -q "25 checks passed, 0 failed" /tmp/run_all_sqrt6_chain.py.log || { echo "FAIL  sqrt6_chain.py count"; fail=1; }
grep -q "41 checks passed, 0 failed" /tmp/run_all_fricke_families.py.log || { echo "FAIL  fricke_families.py count"; fail=1; }
grep -q "kummer_type: 15 checks passed, 0 failed" /tmp/run_all_kummer_type.py.log || { echo "FAIL  kummer_type.py count"; fail=1; }
if [ $fail -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $fail
