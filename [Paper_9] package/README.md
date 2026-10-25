# Paper 9 — Hodge research audit, release v2.8.0

The dependency objection was checked: the three withdrawn preprints are
conditional inputs in the cited H8 discussion, not assumptions needed for
the direct HC/F2/F3′ reduction. A repaired proof of F2 ⇒ AB is provided.
It assumes F2 and does not establish F2.

Start with `HODGE-DEPENDENCY-AND-CLOSURE-AUDIT.md`.

Contents:

- `F2-REDUCTION-REPAIR.md`: the geometric affine-difference argument,
  with its precise assumptions.
- `F3PRIME-EXACT-OBLIGATION.md`: a semisimplicity argument for the abelian
  image and the remaining global requirement.
- `mumford_exact.py` and `mumford-exact-results.json`: exact rational
  matrix and independent character checks; two exceptional directions
  remain after divisor products.
- `lean/AffineReduction.lean`, `lean-compile.log`, `lean-build.json`:
  three elementary subspace lemmas; not a geometric formalisation.
- `AI_PROVENANCE.md`: scope of AI assistance and review status.
- `AUDIT-STATUS.json`, `MANIFEST.json`: status and file integrity.

Reproduce the exact calculation with Python 3:

    python mumford_exact.py

The Lean source needs Lean 4.34.1 and the Mathlib version pinned in
`AUDIT-STATUS.json`; use the standard Mathlib project setup. `compile.py`
records the local installation/cache paths used for this run, so it needs
path adjustment on another machine.

This is an audit folder, not an upload-ready claim of a full Hodge proof.
The two required Mumford cycle classes, global F2, and global F3′ remain
unproved. This supplement is published as GitHub release v2.8.0. Its Zenodo DOI is
recorded in the release description and the publication receipt once issued.
No new Hexagon identifier or journal acceptance is claimed. Existing Papers 1–8 and their packages are left intact.

## Rebuilding the auxiliary Lean lemmas

The nested `lean/` directory is a standalone Lake project. With Lean
available, run there:

    lake update
    lake exe cache get
    lake env lean AffineReduction.lean

The pinned Mathlib revision is recorded in `lakefile.toml`. The
original `compile.py` records the machine-specific cache used for
the supplied successful log. These are three subspace lemmas only.
