# AI provenance

Paper: *Dense Algebraic Loci of Hodge Classes*, Deep Bhattacharjee and Ushashi Bhattacharya.

## What was done with AI assistance

The constructions on (F2) and (F3'), the search for a closure of the Hodge
conjecture, the text of the paper, the figures, the Lean 4 file and the
Python, Julia, C, C++ and shell programs were carried out by Deep
Bhattacharjee with the help of AI assistance (Claude, Anthropic), in sessions
in the Claude Code environment. The mathematical content was checked as
follows.

* Every hand proof in the paper was read against the cited literature
  (Markman, van Geemen, Schütt, Varesco, Buskin, Bloch, Buchweitz, Flenner,
  Moonen, Zarhin, André, Milne) and the earlier paper of the authors with
  Priyabrata Mandal.
* Every finite quantity (closures of the 256 subsets, Hilbert symbols and
  Hasse invariants, the 165 forms over Q(sqrt 6), the Fricke discriminants
  and Picard numbers, the dimension counts 57, 104 and 26, the Hecke algebra
  dimensions) is recomputed by programs in `code/` in at least two languages
  and the combinatorial and arithmetic ones are proved in
  `lean/HodgeClosure.lean` (fifty-nine theorems, forty-nine of them free of
  every axiom, two depending on propext and Quot.sound only, and eight on
  propext only; `native_decide` is not used).
* Two numerical ranks (`product_object.py`, `convolution_checks.py`) are
  computed in floating point; no statement of the paper rests on them. The
  rank behind Theorem VI.6 is also computed exactly (`annihilator_exact.py`),
  the Riemann-Roch polynomial and the thirty-one supports of Proposition VI.7
  (`riemann_roch_pieces.py`), and the invariants of the trace form behind
  Theorem V.12 (`zeta9_invariants.py`), with the Ext groups and chains at the
  CM point of Appendix A (`cm_point_ext.py`, Lean Section 6). A fourth
  round of AI sessions added Lemma VI.9 and Proposition VI.11 (convolutions
  with three line bundles fail at E_0^6); its claim that no Massey product
  had been computed was kept as stated, and the configurations it leaves
  are listed as open in the paper. A fifth round (release v2.0.0) added
  Lemma VI.12 and Proposition VI.13: a lower bound for dim Ext^2 by
  isolated Ext blocks, valid for every twisting cochain, computed over every
  configuration of the four open kinds in a window of twists and shifts
  (`cm_point_counts.py`; the six least values are proved in Lean Section 7
  with a kernel-checked reachability certificate), and Remark V.14 on the
  shape a chain for sqrt 10 would need. The bound settles every placement of
  the thirty-five pieces and two threefolds at one shift meeting along a
  surface; for the other two kinds it is 0 and decides nothing. A sixth
  round added Proposition VI.14 and Corollary VI.15: a threefold piece
  outside every closed chain of Ext blocks fails the criterion for every
  twisting cochain, which settles four line bundles, five line bundles and
  every further piece of positive twist within one shift of the thirty-two
  threefolds (`cm_point_chains.py`; the counts, the entering edges and the
  six-cycles are proved in Lean Section 7). The same round corrected the
  earlier statement that four line bundles are decided by a sixfold Massey
  product: the chain described does not exist when the threefolds have twist
  0, and no closed chain at all exists with four line bundles. The candidate
  configurations (a), (c), (d) and the quotient chains of Proposition V.14
  came from the candidate record of the Anaxia engine of the BLLM project
  (creelie/eBLLM, release v3.0.5, doi:10.5281/zenodo.23469389), whose
  record of configuration (a) carried the same wrong chain; the engine
  proposes, and the proofs and programs decide. The paper now cites the
  engine in a footnote, the bibliography and the data availability section.
  A seventh round added Section VI.G, Setting VI.17 to Remark VI.25,
  with hand proofs throughout: every threefold piece of an object meeting
  the criterion lies on a directed cycle of Ext blocks with exactly one
  edge on which the twisting cochain vanishes, through pieces of both
  parities of shift (Lemma VI.18 to Lemma VI.21); the shape of such cycles
  (Lemma VI.22); and Theorem VI.23, that for every hermitian polarisation
  of E_0^6 a convolution of distinct threefolds and at most five line
  bundles, at any twists, fails the criterion. The enumeration of six,
  seven and eight line bundles (`line_bundle_chains.py`; six and seven
  fail, eight outside thirty-one arrangements, whose ranks the program
  reports) is stated in the paper as a computation of the archive, Remark
  VI.25, and no proved statement rests on it. The enumeration was first
  run on the graph of the engine, as its record C8; its rules were then
  proved in the text and the counts recomputed by the program of the
  archive. An eighth round added Section VI.H, Lemma VI.26 to Proposition
  VI.36, on the support of an object meeting the criterion, with hand
  proofs throughout: the localised Chern character of the support, the
  class of a threefold in local cohomology (Lemma VI.26); the rest of the
  support cuts every threefold of nonzero multiplicity in an ample divisor
  (Theorem VI.27); two threefolds of the same family meeting along a
  surface carry nothing (Theorem VI.29); objects supported on the
  thirty-two threefolds of one family fail (Corollary VI.31); a smooth
  complete intersection cannot carry the rest (Proposition VI.35); an
  ample divisor in the support empties the localised obstruction
  (Proposition VI.36). A ninth round added Lemma VI.32 and Theorem
  VI.33 to the same section: along each line of four threefolds through
  a surface the multiplicities satisfy two linear relations, read off
  from the second summand of the localised obstruction on the surface
  B_j, where the four curves form an ample divisor, so that the
  multiplicities are m a^2; and no object supported on all sixty-four
  threefolds, of both families, has the polarised shape and meets the
  criterion, because the alternating sum of the sixty-four classes is
  zero. The identities of signs and residues used in the section are
  checked by `threefold_supports.py` (sixteen checks). The intersection
  and localisation arguments were proposed in the engine's record C8
  (release v3.1.0, doi:10.5281/zenodo.23484160) and proved in the text;
  the line relations were found in the same engine run on the mixed
  supports that Corollary VI.31 left open.
* The theorem on real multiplication by Q(zeta_9)^+ was found in a second
  round of AI sessions and checked against van Geemen and Schütt (2025,
  Sections 4.8 and 5.6), van Geemen (2008, Remark 7.9), Reiner's Maximal
  orders (Theorem 33.15) and Platonov and Rapinchuk (Theorem 7.8). The
  extension to Q(zeta_7)^+ through the Dickson deformation of the family of
  Artebani, Sarti and Taki (2011, Example 6.1 and Table 3), and the
  proposition on where the dihedral mechanism stops, were found in a third
  round; the invariants of the trace form are recomputed in
  `zeta7_invariants.py` and the Dickson identities, the inertness of 2 and
  the sign pattern of the conjugates are proved in Lean.

## What the AI did not do

The AI did not prove (F2), (F3') or the Hodge conjecture; the paper says so
and states at which step each construction stops. No result of the paper is
reported as proved on the strength of a machine computation alone.

## Where the AI was wrong and corrected

During the work three slips were found by the machine checks and corrected
in the text before release: the Hasse invariant at 2 of the form V_2
(it is -1, not +1); the Picard number of the twist family at level 5 (the
base change adds four fibres of type III); and the dimension of the dihedral
Hecke algebra ((n+1)/2, not (n+3)/2).

## Approval

Both authors approved the final version. Funding: none. Competing
interests: none.
