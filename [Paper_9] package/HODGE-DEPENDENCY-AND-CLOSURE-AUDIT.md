# Hodge v2: dependency audit and targeted proof work

Audit date: 25 October 2026.

**The full rational Hodge conjecture, F2 and F3′ have not been proved in
this work. The two exceptional Mumford directions have not been supplied
with algebraic representatives. This folder is a research audit, not a
submission claiming a complete solution.**

Authors of the existing manuscript remain Deep Bhattacharjee and Ushashi
Bhattacharya. This audit does not change their published manuscript or
their authorship declarations.

## The user's dependency objection is justified

The three withdrawn OpenAI manuscripts concern split Weil eightfolds,
general Kuga–Satake algebraicity, and arbitrary products of K3 surfaces.
The authors' primary notice of 7 October 2026 identifies a sign error in
the stabilisation-trace argument and withdraws the three constructions.
Withdrawal is not a counterexample to those mathematical statements.

The cited H8 v5.0.1 source has a separate section, `13b_preprints.tex`,
entitled “Consequences of recent preprints”. Its opening paragraph makes
the deductions there conditional on the specific cited theorems and
explicitly separates them from results outside that section. In that
section P2, P3 and P4 are the three relevant inputs. These labels should
not be confused with H8's use of P2 for a proposed semiregularity criterion
elsewhere in the manuscript.

The local v2.7.0 Hodge source examined here has no direct OpenAI citation
and no invocation of those three withdrawn results as a proved input.
Its main reduction can be supported without them:

    HC ⇔ (AB and F3′),       F2 ⇔ AB.

Here AB is the Hodge conjecture for all complex abelian varieties. The
first equivalence follows directly by composing algebraic
correspondences. The second has the repaired proof in
`F2-REDUCTION-REPAIR.md`. Therefore a blanket claim that removing the three
preprints destroys this reduction would be incorrect. This conclusion is
not a verification of every theorem in either H8 or Hodge v2.

By contrast, a deduction whose premise actually is one of the withdrawn
statements remains conditional until that premise is independently
established. A theorem of the form “if P then Q” survives as an implication;
it does not establish Q after P loses its supporting proof.

## Exact scope of the source comparison

The posted preprint is https://hexagonmath.org/2610.00315v2. Its PDF was
opened directly; it has 81 pages and explicitly leaves both statements
open. The following local archive has an abstract matching the posted
v2, including the Fricke CM sign, eightfold-shift enumeration, Prym-map
and mass-gap additions:

    D:\Hexagon\JHEP QG\HodgeConjecture-v2.7.0\hexagon\HodgeConjecture_tex.zip
    SHA256 87187ab78d54f98f74e6e98e25a2c34c830a457400ca12b32236fadee0845614

The similarly named archive in `Hexagon v2 Hodge Package` is an older
local source snapshot with different claims about the Fricke families:

    D:\Hexagon\Hexagon v2 Hodge Package\HodgeConjecture_tex.zip
    SHA256 f7e89b50cc42e3a23c125aebc866e856baf646033b65d914d6d5fd6abc538301

Both were inspected; findings below use the v2.7.0 source. Remote Hexagon
source download could not be independently fetched, so byte identity
between the local ZIP and the server's ZIP is not asserted. References
below use TeX labels to avoid ambiguity from changed theorem numbering.

## Targeted constructions and checks

1. **Repair of the reduction.** The original `thm:f2isab` proof uses a
   replacement g → g² that can remove the inequality it needs. An affine
   difference construction avoids this step and avoids an unsupported
   inference that F2 immediately makes every degree-twelve Hodge class
   algebraic. For β ∈ R(A), put η = aᵖ ⊠ e and δ = β ⊠ b² on
   A × (X × X). The two classes η and η + δ are outside R and hence
   algebraic **assuming F2**. Their difference and a pushforward recover
   β. The detailed proof records the geometric inputs and its limitation.

2. **Independent exact Mumford count.** `mumford_exact.py` constructs all
   six raising/lowering operators of sl₂³ on the weight-zero part of
   Λ⁴(V ⊕ V), V = 2 ⊗ 2 ⊗ 2. Its matrix has 132 columns and 480 rows.
   Exact rational kernel computation gives dimension 8. The products of
   the three divisor forms span dimension 6. Two complementary invariant
   directions are stored explicitly in the split model. Independent Weyl
   character extraction also gives 8. This verifies the two-dimensional
   target; it does not construct subvarieties or identify the split-model
   coordinate vectors with rational cycles on a particular Mumford fibre.

3. **Sixfold counts and a direction error.** Exact character computation
   reproduces 3 invariants in H²(Z) and 26 invariants in H⁴(X × X × Z)
   for the full group G × K¹ in the split model. If the actual Hodge
   group is contained in that group, the invariant space can get larger.
   Thus containment supplies lower bounds, not the upper bound claimed
   in the proof of `thm:link`(i). Equality requires an additional equality
   of groups or a separate upper-bound argument. Likewise `lem:polarisations`
   does not establish Picard number exactly 3 from containment alone.
   As a group-theoretic control, restricting to a maximal torus gives 6
   and 291 in the same two degrees. These numbers are not claimed to be
   the actual Hodge numbers at a specified geometric point.

4. **Specialisation is not propagation.** A cycle at a special fibre
   does not itself give a dominating component of the relative Hilbert
   scheme. The proof of `thm:link`(iii), asserting passage from one point
   to all points of C, needs the exact hypotheses of its propagation
   reference checked. The dichotomy lemma by itself gives a countable
   algebraic locus or the whole curve. Dense countable sets do not resolve
   that alternative. A Hecke-invariant dense set alone is also insufficient.

5. **Blow-ups retain the original obstruction.** The established formula
   for a smooth centre Z of codimension c is

       Hdgᵖ(Bl_Z X)/Algᵖ(Bl_Z X)
          ≅ Hdgᵖ(X)/Algᵖ(X) ⊕ ⨁_{i=1}^{c−1} Hdgᵖ⁻ⁱ(Z)/Algᵖ⁻ⁱ(Z).

   Hence a blow-up cannot kill a class pulled back from X. This does not
   prove a monotonicity statement for arbitrary sequences that also
   contain blow-downs; the reverse operation removes the exceptional
   summands. In codimension 2 those new summands vanish by the (1,1)
   theorem, so the codimension-two defect is birationally invariant.

6. **Unknown is not non-algebraic.** The sentence in `sec8_status.tex`
   calling the open classes “not algebraic” must instead say that their
   algebraicity has not been established. Proving them non-algebraic would
   disprove the rational Hodge conjecture, which this manuscript does not do.

## What would actually close the conjecture

For the first Mumford target, construct rational algebraic cycles whose
classes span the two exceptional directions and verify the cycle-class
identities on the actual family. The sixfold link route instead needs an
algebraic representative for its mixed class ξ, plus the exact hypotheses
of the adjoint and propagation arguments. Counting invariant vectors does
not provide such a representative.

That would settle an important special case. It would still not prove
F2 for every abelian variety, or F3′ for every smooth projective variety.
The global quantifiers cannot be replaced by the first example. In the
Weil-sheaf route, the required Ext algebra and injective semiregularity
map remain proof obligations; in the general F3′ route, one still needs
the stated algebraic correspondences from abelian varieties.

The residue and mass-gap reformulations in Section 8 do not supply these
missing cycles. In particular, existence of a mass minimiser proves an
inequality. Calibration equality for an appropriate multiple of the Hodge
class is precisely the additional conclusion that remains to be proved.

## Verification and publication status

The exact arithmetic checks passed. The three auxiliary Lean lemmas are
reported separately in `lean-build.json`; they concern subspaces and
affine differences, not algebraic geometry. Neither check is a formal
proof of HC, F2 or F3′.

No full-closure manuscript, journal submission, GitHub release or new DOI
is produced by this audit. Existing submission packages remain intact.

## Primary sources checked

- Posted Hodge v2: https://hexagonmath.org/2610.00315v2
- H8 v5.0.1: https://github.com/creelie/H8/releases/tag/v5.0.1
- Withdrawal notice: https://github.com/openai/math/blob/main/history.md
- Markman's sixfold/fourfold result: https://arxiv.org/abs/2502.03415
- Markman's survey, including its dimension restrictions:
  https://arxiv.org/abs/2509.23403
- Moonen–Zarhin on low-dimensional Hodge groups:
  https://arxiv.org/abs/math/9901113

Downloaded H8 sources are pinned to v5.0.1; their tree and file hashes
are retained in the working audit directory. The two known Markman
arXiv manuscripts are distinct from the three withdrawn OpenAI papers.
