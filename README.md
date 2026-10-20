# Dense Algebraic Loci of Hodge Classes

Deep Bhattacharjee and Ushashi Bhattacharya

This repository holds the paper, its figures, the Lean 4 certificate and the
programs that recompute every finite quantity used in the proofs.

## What the paper proves

* The Hodge conjecture is equivalent to the conjunction of two statements
  about abelian varieties, (F2) and (F3'), and (F2) is equivalent to the
  Hodge conjecture for abelian varieties. Of the 256 subsets of the eight
  statements of the closure graph, 230 imply the conjecture, and exactly six
  are minimal: {F3}, {L, M}, {L, F3'}, {V, F3'}, {F2, F3'}, {AB, F3'}.
* For each statement the set of members of a family on which it is known is
  dense and is either the whole family or meagre; (F2) is equivalent to the
  propagation of algebraicity from CM points along polarised abelian schemes.
* Real multiplication by sqrt 6 on K3 surfaces is algebraic on two
  two-dimensional families (a chain of symplectic quotients); real
  multiplication by sqrt 5 and sqrt 7 is algebraic on the one-dimensional
  Fricke families over X_0(5) and X_0(7) (fibrewise isogenies of elliptic K3
  surfaces). Hodge similarities act with multiplier d_1 d_2; finite-group
  correspondences give abelian endomorphism fields; the Hodge conjecture
  holds for X x X when X lies in a dihedral family.
* A complex on a product of two Weil fourfolds has the Chern character the
  polarised semiregularity criterion asks for; direct sums are never
  semiregular, and convolutions with mismatched slopes are obstructed. At the
  point of complex multiplication E_0^6 every Ext group between the pieces
  is computed, no diagonal class cancels in two steps, and every convolution
  built from at most three line bundles and threefolds meeting in finite sets
  fails the criterion. A count of isolated Ext blocks, valid for every
  twisting cochain, settles every placement of those thirty-five pieces
  (dim Ext^2 >= 2605) and two threefolds at one shift meeting along a surface
  (dim Ext^2 >= 5325); and one threefold piece outside every closed chain of
  Ext blocks already fails the criterion, which settles every further piece
  of positive twist within one shift of the thirty-two threefolds. For every
  polarisation of E_0^6, a convolution of distinct threefolds and at most
  five line bundles at any twists fails the criterion (by hand: every
  threefold piece must lie on a cycle of Ext blocks that carries a Massey
  product, of both parities of shift, and with five line bundles the
  Maurer-Cartan equation leaves no such cycle); the enumeration of the
  archive extends this to six and seven line bundles and to eight outside
  thirty-one arrangements. An object meeting the criterion cannot be a
  shifted line bundle on a threefold off a divisor that is not ample, and its
  threefolds form a set closed under sign changes. What remains at E_0^6 are
  eight or more line bundles and a threefold at several twists, decided by
  the products along their chains, which are not computed.
* A single class on an abelian fourteenfold carries the exceptional classes
  of a Mumford fourfold.
* Specialisation, degeneration and blow-ups relocate the two open statements
  without weakening them.

Neither (F2) nor (F3') is proved, and the paper does not claim the Hodge
conjecture. Section VIII says at which step each construction stops, and
Section VII records where the earlier preprint
(doi:10.20944/preprints202602.0462.v5) fails.

## Layout

```
paper/                      REVTeX source, figures and the compiled main.pdf;
                            main_journal.tex is the one-column (amsart) build
preprints/                  the compiled paper only
lean/HodgeClosure.lean      59 theorems (Lean 4.24.0, no Mathlib)
code/                       Python, Julia, C, C++ and shell checks; run_all.sh
```

## Running the checks

```
cd code && ./run_all.sh
```

Requirements: python3 with sympy, numpy and mpmath; julia; a C and a C++
compiler; lean (through elan; `lean/lean-toolchain` pins the version). Set
`JULIA`, `CC`, `CXX` or `LEAN` to override the commands. The run takes about
thirty minutes and ends with `ALL CHECKS PASSED`. `code/EXPECTED.md` lists each
program, what it checks and its expected output. The Lean file prints
`#print axioms` for every theorem: forty-nine use no axiom, two use
`propext` and `Quot.sound`, and the six isolated-block counts and two
chain-free counts of Section 7 use `propext`; `native_decide` is not used.

No statement proved in the paper rests on these checks; the enumerations of
Proposition VI.13 and Remark VI.25 are their output and are stated as such,
and the rest guard the hand computations. The candidate configurations at E_0^6 were proposed by Anaxia,
the construction engine of the BLLM project
([creelie/eBLLM](https://github.com/creelie/eBLLM), release v3.0.5,
doi:10.5281/zenodo.23469389), and the support results of Section VI.H by its
release v3.1.0 (doi:10.5281/zenodo.23484160); the engine proposes, and the
proofs and these programs decide.

## Building the paper

```
cd paper && latexmk -pdf main.tex
```

The figures are generated by `code/make_figures.py` (matplotlib).

## Archive

| release | DOI |
| --- | --- |
| concept (all versions) | [10.5281/zenodo.23439577](https://doi.org/10.5281/zenodo.23439577) |
| v1.0.0 (17 October 2026) | [10.5281/zenodo.23439578](https://doi.org/10.5281/zenodo.23439578) |
| v2.0.0 (19 October 2026) | [10.5281/zenodo.23461752](https://doi.org/10.5281/zenodo.23461752) |
| v2.0.1 (19 October 2026, records the v2.0.0 DOI) | [10.5281/zenodo.23461820](https://doi.org/10.5281/zenodo.23461820) |
| v2.1.0 (19 October 2026) | [10.5281/zenodo.23483266](https://doi.org/10.5281/zenodo.23483266) |
| v2.1.1 (19 October 2026, records the v2.1.0 DOI) | [10.5281/zenodo.23483297](https://doi.org/10.5281/zenodo.23483297) |
| v2.2.0 (19 October 2026, Section VI.H on supports) | [10.5281/zenodo.23485778](https://doi.org/10.5281/zenodo.23485778) |
| v2.3.0 (20 October 2026, Theorem VI.33 on the sixty-four threefolds) | [10.5281/zenodo.23486524](https://doi.org/10.5281/zenodo.23486524) |

## Licence

MIT, see `LICENSE`.
