# Hodge Classes on Abelian Varieties and Beyond

Deep Bhattacharjee and Ushashi Bhattacharya · Complete manuscript version 7 · Release v3.1.1

The 104-page revision retains the full earlier v7, its 205 labels and all 14 original figure files. It adds fully derived transfer and propagation results, diagrams, footnotes and a new appendix. **Universal F2 and F3-prime and the general rational Hodge conjecture remain unproved.**

- [Paper PDF](papers/hodgefinal.pdf)
- [Standalone TeX ZIP](papers/texfinal.zip) — compile main.tex with pdfLaTeX, three passes.
- [Release v3.1.1](https://github.com/creelie/fermat-hodge-/releases/tag/v3.1.1)
- [Zenodo version DOI](https://doi.org/10.5281/zenodo.24023964)
- [Original posted v6](https://doi.org/10.20944/preprints202602.0462.v6)

## Added proofs

Bounded cycle-support degree gives a closed representability locus, automatic common denominators and a total-space algebraic cycle whenever that locus is dense. A detected support suffices under the explicit constant-subsystem hypothesis; tracing arbitrary nonzero varying classes would not suffice. No uniform support-degree bound for the mixed Mumford class has been proved.

Exact correspondence formulas split the algebraicity and abelian-transfer defects under blow-ups, projective bundles and finite covers. A divisor-intersection matrix gives an algebraic projector onto the nonprimitive divisor part of rational Hodge classes in degree four. Its complement reduces F3-prime to primitive classes without assuming an algebraic inverse Lefschetz operator on all cohomology. It does not prove that primitive defect vanishes.

## Verification and reproduction

The source ZIP includes every TeX input and figure. The new finite checks use rational arithmetic:

```sh
python papers/checks/check_weights.py
python papers/checks/check_transfer.py
```

These verify finite identities, not geometric existence or the universal conjecture. The new geometry is not Lean-formalized; the previous Lean material retains its stated finite scope. Computational and AI assistance is recorded separately from human authorship. No novelty priority or journal acceptance is asserted. The paper is CC BY 4.0; existing MIT code notices are retained.

The immutable tag was archived with the concept DOI. The attached paper and TeX ZIP carry the subsequently verified version DOI; the mathematical content is unchanged.
