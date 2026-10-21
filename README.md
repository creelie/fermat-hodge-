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
  two-dimensional families (a chain of symplectic quotients). The fibrewise
  isogenies of the one-dimensional Fricke families over X_0(5) and X_0(7)
  are complex multiplications by Q(sqrt -5) and Q(sqrt -7), not real ones:
  the sign of the square of the isogeny is decided by how the twisting
  function behaves under the Fricke involution, -N for the pair twists that
  form the families and +N only at the fixed-point twists, which are the two
  surfaces of van Geemen and Schutt. So every member has complex
  multiplication, the Hodge conjecture holds on every power and every
  Hilbert scheme of every member (Ramon Mari, Varesco) and (F3') with it,
  and the very general member has Picard number 16 by point counts over
  F_11 and F_7 (an archive computation, stated as such). Hodge similarities
  act with multiplier d_1 d_2; finite-group correspondences give abelian
  endomorphism fields; the Hodge conjecture holds for X x X when X lies in
  a dihedral family. On the higher powers the Hodge conjecture for the
  surfaces with totally real endomorphism field reduces to Varesco's
  exceptional classes, and it holds, with (F3'), on every power and Hilbert
  scheme of a K3 surface of Kummer type over Q, a condition read off the
  Hasse invariants of the transcendental lattice at Picard numbers 17 and
  18. The transcendental spaces of the Fricke surfaces are
  U^2 + <-1> + <-N>, so their Kuga-Satake varieties are fourth powers of an
  abelian fourfold B of Q(sqrt -N)-Weil type of discriminant one, and B is
  isogenous to the product of an elliptic curve with complex multiplication
  by Q(sqrt -N) and a simple threefold with endomorphism field Q(sqrt -N).
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
* At the point E_0^8 of complex multiplication, a convolution of the 128 Weil
  line bundles whose shifts form two adjacent pairs at any distance fails the
  criterion (Proposition VI.37), and so does every convolution whose shifts
  lie in seven consecutive integers in eighteen of the twenty-eight
  arrangements (Corollary VI.38); an archive computation, stated as such,
  decides nine others (Remark VI.39, least bound 125.8 > 104) and leaves
  one open: even shifts s, s-2, s-4, s-6 with odd shifts s-1, s-5.
* The curve x^3 + y^3 + 1 + lambda x^3 y^3 = 0 of genus four with
  eta = O(1,-1) of order three makes the multiplication map
  H^0(K + eta) x H^0(K - eta) -> H^0(2K) an isomorphism, so the period map
  of cyclic triple covers of genus-four curves is a local isomorphism onto
  the Weil domain of Q(sqrt -3) at n = 3 (Proposition VI.40, an explicit
  point for Faber's theorem). Over twelve cubic fields the count of
  sextic CM fields excludes no integral character (Remark VI.41).
* A single class on an abelian fourteenfold carries the exceptional classes
  of a Mumford fourfold.
* Specialisation, degeneration and blow-ups relocate the two open statements
  without weakening them. Residues of Jacobian determinants give the classes
  of complete intersections on hypersurfaces (Proposition VIII.3), and the
  Hodge conjecture for a class alpha is equivalent to the vanishing of the
  mass gap of e alpha + k h^p for integral currents (Proposition VIII.4);
  Kollar's hypersurfaces show that the multiplier e cannot be dropped.

Neither (F2) nor (F3') is proved, and the paper does not claim the Hodge
conjecture. Section VIII says at which step each construction stops, and
Section VII records where the earlier preprint
(doi:10.20944/preprints202602.0462.v5) fails.

## Layout

```
paper/                      REVTeX source, figures and the compiled main.pdf;
                            main_journal.tex is the one-column (amsart) build
paper/paper1/               the compiled paper, HodgeConjecture.pdf
paper/paper2/               the LaTeX source as HodgeConjecture_tex.zip
preprints/                  the compiled paper only
lean/HodgeClosure.lean      62 theorems (Lean 4.24.0, no Mathlib)
code/                       Python, Julia, C, C++ and shell checks; run_all.sh
```

## Running the checks

```
cd code && ./run_all.sh
```

Requirements: python3 with sympy, numpy, scipy and mpmath; julia; a C and a C++
compiler; lean (through elan; `lean/lean-toolchain` pins the version). Set
`JULIA`, `CC`, `CXX` or `LEAN` to override the commands. The run takes about
about four hours, three and a half of them for `efour_seven.py`, and ends with `ALL CHECKS PASSED`. `code/EXPECTED.md` lists each
program, what it checks and its expected output. The Lean file prints
`#print axioms` for every theorem: fifty-two use no axiom, two use
`propext` and `Quot.sound`, and the six isolated-block counts and two
chain-free counts of Section 7 use `propext`; `native_decide` is not used.

No statement proved in the paper rests on these checks; the enumerations of
Proposition VI.13 and Remarks VI.25, VI.39 and VI.41 are their output and are stated as such,
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
| v2.4.0 (20 October 2026, Propositions V.14, V.15 on the powers of K3 surfaces and Kummer type) | [10.5281/zenodo.23487336](https://doi.org/10.5281/zenodo.23487336) |
| v2.4.1 (20 October 2026, records the v2.4.0 DOI) | [10.5281/zenodo.23487369](https://doi.org/10.5281/zenodo.23487369) |
| v2.5.0 (20 October 2026, Proposition V.17 on the exceptional classes of the Fricke surfaces) | [10.5281/zenodo.23488135](https://doi.org/10.5281/zenodo.23488135) |
| v2.6.0 (20 October 2026, Theorem V.9 corrected: the Fricke families carry complex multiplication by Q(sqrt -5), Q(sqrt -7), with the Hodge conjecture on all their powers) | [10.5281/zenodo.23490234](https://doi.org/10.5281/zenodo.23490234) |
| v2.7.0 (21 October 2026, seven shifts at E_0^8, the genus-four cover, residues and mass-minimising currents) | to be recorded |

## Licence

MIT, see `LICENSE`.
