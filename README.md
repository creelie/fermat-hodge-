# Dense Algebraic Loci of Hodge Classes

Complete version 7 research revision — GitHub release v3.0.0.

**F2, F3′, the generic mixed Mumford–sixfold correspondence and the general rational Hodge conjecture remain unproved.**

The complete manuscript retains all 45 section/subsection headings, all 164 labels, all 14 figure files and both appendices of the supplied v6, with explicit corrections and integrated additions. It is not the earlier 15-page focused rewrite.

## Current files

- [Complete manuscript](papers/hodgefinal.pdf)
- [Compilable TeX source ZIP](papers/texfinal.zip) — compile `main.tex` with pdfLaTeX.
- [Exact checks and scope](papers/checks/package-verification.json)
- [Retention and correction manifest](papers/checks/full-v7-retention.json)
- [Repository evidence audit](papers/REPOSITORY-EVIDENCE.md)
- [AI provenance](papers/aiprovenance.md)

## New constructions and tests

The matched CM choice gives `X_c ~ E × B` and `Z_c ~ E³ × B`; Markman's published discriminant-one theorem and an all-degree weight argument algebraize the mixed link at that fibre and on its dense rational-isogeny orbit. The adjoint projector and cubic field action on the auxiliary sixfold are algebraic. A nonzero algebraic link, or one exceptional algebraic class on the full-group Mumford square, would give the conjecture on all powers of that fourfold by explicit partial-transpose tensor operations.

The new K3 example has `E = L ⊕ L⁻¹`, constant total character `2 − 36[point]`, and a nonzero first-order deformation obstruction in the trace kernel. Thus preservation of the full Chern character does not by itself deform a chosen representative. A separate blow-up argument explains why a theorem for every rational smooth projective variety would already supply universal F3′.

Five exact Python checks verify finite representation identities. These are not a Lean formalisation of the geometric arguments or a proof of the general conjecture. The original verification programs and Lean material remain in their existing repository paths.

## Archives and preprints

- [Release v3.0.0](https://github.com/creelie/fermat-hodge-/releases/tag/v3.0.0)
- [Zenodo version DOI](https://doi.org/10.5281/zenodo.24020080)
- [Zenodo concept DOI](https://doi.org/10.5281/zenodo.23439577)
- [Supplied posted v6](https://doi.org/10.20944/preprints202602.0462.v6)
- [Earlier Hexagon record](https://hexagonmath.org/2610.00315v2)
- [Previous archive v2.9.1](https://doi.org/10.5281/zenodo.23790334)

The source tag records the concept DOI. The release PDF and source ZIP now include the verified version DOI **10.5281/zenodo.24020080**. This bibliographical imprint was added after the immutable source tag was archived; the mathematical content is unchanged.

Authors: Deep Bhattacharjee and Ushashi Bhattacharya. Computational and language-model assistance is described in the provenance file; the tools are not authors. No novelty priority, full formalisation, journal acceptance or general-conjecture resolution is asserted.
