# Research notes for v7

The specific flat mixed class on the Mumford fourfold square times the auxiliary sixfold is represented at a matched CM fibre. The argument deliberately chooses the same compositum field for the left CM torus and the right action on the sixfold. The rational norm morphism identifies their weight decompositions. The exceptional tetrahedra on the CM fourfold are discriminant-one Weil classes, so the seed uses a published theorem of Markman. The rank-nine projector on the sixfold and its field action are obtained directly from algebraic endomorphisms and divisor classes.

## Source checks

- [Markman, JEMS, Theorem 1.5](https://ems.press/journals/jems/articles/4732564) applies to the determinant classes on every polarized discriminant-one Weil fourfold. The draft constructs that discriminant by rescaling the elliptic factor. It does not invoke the later general fourfold preprint for the seed.
- [The October OpenAI CM manuscript](https://github.com/openai/math/tree/main/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026) concerns CM abelian varieties. Its stated result would supply algebraic classes at CM points, with the same propagation problem for full-group fibres. The draft does not use it as an input.
- [OpenAI's release history](https://github.com/openai/math/blob/main/history.md) records withdrawals of the general K3 Kuga–Satake and K3-product proofs following a sign error in their input. The [remaining quadratic-locus preprint](https://github.com/openai/math/tree/main/preprints/Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026) uses an ambient quadratic space of rank eight, so cannot contain the rank-nine carrier considered here.
- [Floccari and Fu, arXiv:2610.31740](https://arxiv.org/abs/2610.31740) treat stated generalized Kummer families. Their hypotheses do not supply the mixed Mumford-sixfold correspondence.

## Where the construction stops

The isogeny used at the seed cannot persist at full-group fibres, where the weight-one representations have no common summand. The final degree-four class could still have an algebraic representative there. A bounded-degree representative on infinitely many fibres, or a representative whose deformation space dominates the curve, would resolve that step. Neither assertion follows from the density of the isogeny orbit. Even that propagation would settle a particular family on the abelian side and leave the universal statements (F2) and (F3′) open.

The v7 first-order test makes this failure infinitesimal. A rational CM Hodge morphism that commutes with the period derivative at the split real place must commute with its Galois-conjugate root lines at all three places. It would therefore intertwine the full derived group, which has no such cross morphism. This concerns the homomorphisms in the seed recipe. It leaves the deformation of the resulting mixed cycle open.

An Adams-operation projector constructs a perfect complex whose cohomological Chern character is exactly a positive integer multiple of the mixed degree-four class, with all other components zero. This resolves the requirement that every Chern component stay Hodge. The self-extension obstruction and the injectivity of its semiregularity map still require a calculation on an actual representative.

## Relation to F2 and F3′

The matched CM theorem addresses specific fibres of the abelian-side statement F2. The theorem on powers of the auxiliary sixfold addresses another specified abelian family. The theorem on powers of a full-group Mumford fourfold is conditional on one exceptional cycle or one nonzero algebraic mixed link. No new result in this draft proves F2 for every abelian variety. The introductory domination argument proves F3′ for the specified varieties dominated by products of curves, while F3′ for arbitrary varieties remains open. The universal conjecture therefore has both statements as remaining requirements.

The current PDF is the complete v7: all original section/subsection headings, labels and figures are retained, with corrections recorded in `checks/full-v7-retention.json`. The four new construction sections, the explicit bypass audit and Appendix C are integrated into the retained manuscript. The original supplied source ZIPs remain unchanged.

## Verification

The package includes exact Python checks for weight multiplicities, the matched CM character list, the partial-transpose formula, the Adams projector and the root-intertwiner ranks. They cover those finite calculations, not the deformation of a perfect complex or the full Hodge conjecture. The arguments were developed with AI assistance and parallel mathematical reviews. The construction's novelty has not been established by a comprehensive literature review.

## Additional bypass audit

F3′ implies that every rational Hodge class on the target is absolute Hodge, by Deligne's theorem for abelian sources and stability under algebraic correspondences. Replacing the source classes by divisor products already asserts algebraicity of the target class. There is no independent proof of universal F3′ here.

On a smooth Fermat quartic with a line ℓ, put l = 4ℓ − H and L = O(l). Then H·l = 0 and l² = −36. The polystable bundle L ⊕ L⁻¹ has total character 2 − 36[point], preserved under polarized deformation, but a tangent transverse to l's Hodge hyperplane gives obstruction diag(u, −u), u ≠ 0. Its Ext² is C² and semiregularity is (a,b) ↦ a+b. This rules out the proposed inference from character preservation to deformation of the chosen object. It is not a counterexample to HC.

A smooth projective Y embeds in P^N with codimension at least two. The rational variety Bl_Y(P^N) contains h(Y)(−1) through algebraic blow-up correspondences. Thus universal F3′ (or HC) for rational varieties would already give the universal statement. Extending a proved morphism-domination result to arbitrary rational domination would therefore require the original missing theorem.

The Adams-projected pure mixed character has zero degree against a product polarization. It cannot be the total character of a coherent sheaf, and adding rank without changing the other components cannot produce a Hermite–Einstein bundle. These conclusions have those specific hypotheses; they do not rule out arbitrary cycle representatives or other complexes.
