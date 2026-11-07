# Next-version submission notes

Title: Algebraic Hodge Loci and Exceptional Correspondences

Authors in manuscript order: Deep Bhattacharjee; Ushashi Bhattacharya

Submission route: Preprints.org, v6 to v7. The platform version is independent of GitHub release numbering.

Existing record: [v6](https://doi.org/10.20944/preprints202602.0462.v6). The v7 identifier is not claimed to exist before submission is accepted by the platform.

Research release: [v3.4.0](https://github.com/creelie/fermat-hodge-/releases/tag/v3.4.0). Version DOI: [release page](https://github.com/creelie/fermat-hodge-/releases/tag/v3.4.0) (DOI awaiting archive verification).

## Abstract to paste

We construct algebraic Hodge classes in explicit abelian and K3 families and reduce abelian transfer to primitive middle-degree classes on rational varieties. Exact correspondence formulas and bounded-support criteria isolate the generic mixed Mumford class. Its algebraicity and the universal Hodge conjecture remain open.

## Changes in this revision

Adds the explicit primitive middle-degree reduction, including rational blow-up targets. Earlier manuscript material is retained. The title is unchanged. The abstract is shortened. Current submission files replace superseded compiled copies on the main branch.

## Scope that must remain visible

The generic mixed Mumford cycle and universal F2 and F3-prime remain unproved. Moving a class by an algebraic graph or a blow-up does not construct an abelian source for it.

## Files

- `hodge.pdf` is the current compiled manuscript.
- `hodgetex.zip` has `main.tex` at its root, with required figures and ancillary checks.
- `aiprovenance.md` records the origin and checking scope of this revision.
- `release-details.md` identifies the current release and DOI.

Compile with pdfLaTeX at least three times. Upload the TeX ZIP when the platform compiles sources. Do not upload superseded PDFs or use a new-version suffix as an already assigned identifier.

## Checks and declarations

The current source compiles locally. Finite ancillary checks do not prove the remaining existence or uniform estimates. This revision has not supplied a new Lean formalization of its analytic or geometric arguments. The submitting authors must confirm the human-understanding, authorship, licence and platform declarations for the current additions.
