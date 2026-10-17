# Expected outputs

Each program prints `PASS` or `ALL CHECKS PASSED` on success and exits with
status 0.  `run_all.sh` runs all of them and prints one line per program.
Times are those of one run on a 4-core x86-64 machine.

| program | what it checks | expected output | time |
| --- | --- | --- | --- |
| `closure_graph.py` | closures of the 256 subsets of the eight statements, the six minimal sufficient sets, eight sets that do not derive HC | `subsets: 256  deriving HC: 230`, `minimal sufficient sets: 6`, `closure_graph: PASS` | < 1 s |
| `closure_graph.jl`, `closure_graph.c`, `closure_graph.cpp` | the same by three independent implementations | the same two counts and `PASS` | < 1 s each |
| `eigencharacter.jl` | eta(tau x, tau y) = N(tau) eta(x, y) on 1400 instances, N multiplicative, N(2 + sqrt(-d)) != 1, tau^(2n) != N(tau)^n | `eigencharacter.jl: PASS` | 1 s |
| `hilbert.c` | Hilbert symbols, the rank, signature, discriminant and Hasse invariants of the five forms of Table II, the isometry T + <1,-10> = V_3 | every row `matches Table II`, `hilbert.c: PASS` | < 1 s |
| `sqrt6_chain.py` | Hasse-Minkowski classification, the 165 sign-admissible forms over Q(sqrt 6) (98 embed in V_3, 67 do not), the complements, both orders of the chain | `25 checks passed, 0 failed` | 15 s |
| `fricke_families.py` | the Fricke universal curves at levels 5 and 7: fibre types, Euler numbers, Picard bound 16, the Fricke involution on the roots of j, the twist invariance, the lattice step, the dihedral Hecke algebras | `41 checks passed, 0 failed` | 35 s |
| `product_object.py` | the exterior-algebra model of H^*(A x A') at (m,m') = (2,1), (2,2): cross terms, Hankel rank 3, first-order Hodge locus of dimension 9 and 16, r = 57 and 104 | final line lists `'rho': 3, 'aH': 9, 'r': 57` and `'rho': 3, 'aH': 16, 'r': 104` | 2.5 min |
| `convolution_checks.py` | the mixed directions (4 and 8) and the contraction ranks under the orthogonality hypothesis; the trace of an upper times a strictly upper triangular block matrix | `summary: [{'n': 3, 'r': 57, 'rho': 3, 'mixed': 4}, {'n': 4, 'r': 104, 'rho': 3, 'mixed': 8}]` | 4 min |
| `sixfold_link.py` | the sixfold Z_K: alternation and invariance of psi_c, the copy of T, the ratio of the forms at the three places, the count 26, the weight support of xi | `ALL CHECKS PASSED` | 20 s |
| `link_weights.py` | the Hodge classes of degree four on X x X x Z_K under three groups, the action of the cyclic permutation, Hom(X_c, Z_{K,c}) = 0 at the compositum CM point | `ALL CHECKS PASSED` | 1 min |
| `bypass_checks.py` | the Horn closure with the abelian-variety facts of the literature adjoined, Manin's blow-up bookkeeping | `ALL CHECKS PASSED` | < 1 s |
| `zeta9_invariants.py` | the trace form of the quaternion algebra (-1,-theta) over Q(zeta_9)^+ scaled by -theta has the rank, signature, discriminant and Hasse invariants of the transcendental lattice (U + A_2(-1)^4)^perp; three contrasting algebras do not | `MATCH=True` on the predicted line, `MATCH=False` on the contrasts, `zeta9_invariants: PASS` | 4 s |
| `annihilator_exact.py` | exact arithmetic over Q(sqrt -3) at (m,m') = (2,1), (2,2): the identity for ch(E'), the annihilator of ch(E') in T D_{n,n} of dimension m^2 + m'^2, and the same for each component theta_A^k (x) R_k | lines `(2) ... True`, `(3) ... 2mm' ? True`, `annihilator_exact: PASS` | < 1 s |
| `riemann_roch_pieces.py` | the polynomial P(l) = chi(F, L^l), the 31 supports S: a polarised p with P = 0 on its whole support exists only for singletons; the Euler characteristics and the A'-side table | `admissible supports: [(0,), (1,), (2,), (3,), (4,)]`, `riemann_roch_pieces: PASS` | 1 s |
| `../lean/HodgeClosure.lean` | thirty-six theorems; `#print axioms` for each | 34 lines `does not depend on any axioms`, 2 lines `depends on axioms: [propext, Quot.sound]` (`prym_locus_small`, `sum_squares_lt`) | 1 min |

The ranks in `product_object.py` and `convolution_checks.py` are computed in
floating point (singular values with relative tolerance 1e-7); every rank is
an integer and is stable under rerandomisation of the generic data.  No
statement of the paper rests on these two programs.
