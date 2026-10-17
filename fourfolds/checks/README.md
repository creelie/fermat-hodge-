# Re-checks of the finite arithmetic

The proofs of the paper are by hand. The finite arithmetic they use (lists
of residues, sums, character values, block patterns, parities) is certified
by the kernel in `../lean/FermatFourfolds.lean` and re-checked here, from
scratch, in five further languages.

| file | language | what it re-checks |
|---|---|---|
| `finite.py` | Python 3 | every statement of the Lean file |
| `finite.c` | C99 | every statement of the Lean file |
| `finite.cpp` | C++17 | the same, with the standard containers |
| `finite.jl` | Julia 1.10 | every statement of the Lean file |
| `finite.sh` | bash | the balanced multisets, the angle tables, the block patterns, the parity at 110 and the first open degrees |

`bash run_all.sh` builds and runs all five (Julia when `julia` is on the
path), then the Lean file (when `lean` is on the path). Each program ends with `N checks passed, 0 failed` and
exits with a nonzero status on a failure.

What is checked, by section of the paper:

- Section 1: the first degrees not divisible by 110 that the quoted results
  leave open are 228, 258, 260, 266.
- Section 2: the examples of standard multisets and of a lowering move; at
  the levels 21, 28, 33, 35, 39, 44, 52, 66, 78, 102, 110, 114 every pair and
  every standard multiset is balanced.
- Section 4: the orbits O21, O33, O39 by residues, their stabilisers and
  coset representatives, their balance, the identities that make them
  algebraic, and the small facts of the case analysis.
- Section 5: the sets Q(M), and the vanishing of the parity homomorphisms on
  the generators of S_M at the levels 114, 102, 44, 52, 33, 35, 39.
- Section 6: the five pairs of characters (entry sums, the condition on
  every unit, the printed tables, the joined multiset, no pair, the parity),
  and the eight block patterns (P1), (P2), (P3) with their weights.
- Section 8: the small levels 20, 28, 44, 140 of Shape III.
- Section 9: the sextuple A110, its parity, and the vanishing of that
  parity on S_110.
- Section 10: the rows of the table of small local configurations.
