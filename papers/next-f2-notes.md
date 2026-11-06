# Next F2 propagation result and scope

The separate next-f2-proof.tex supplies three proved refinements. No existing manuscript was edited.

1. **Automatic arithmetic bounds.** The fixed-support-degree locus Sigma_D is closed on an arbitrary smooth irreducible base. Finitely many proper Chow components automatically supply one common denominator N_D and a bound on the degrees of the positive and negative integral cycles representing N_D gamma. Initially unbounded rational coefficients cause no additional obstruction once support degrees are bounded.
2. **Actual globalization.** A dense bounded-degree locus produces one rational algebraic cycle on the total space by taking a finite generic multisection, tracing its cycles, dividing by the degree, and closing up. Equivalent formulations are nonmeagre algebraicity, algebraicity at all fibres, one global support-degree bound, and a total-space cycle restricting to the given flat class.
3. **Weaker mixed-link test.** In the Mumford/sixfold setting it is sufficient to find one support of uniformly bounded degree with nonzero mixed projection at infinitely many distinct fibres. It is unnecessary to express xi itself in the rational span of those bounded-degree supports beforehand.

The third statement requires the proof's constant-subsystem condition. A trace of nonzero classes in a general varying local system can cancel. Here the projected generic Hodge classes form the constant subsystem F xi. On a dominating Chow component the projected class is a fixed e xi, e nonzero; all conjugates have that same class, so trace cannot cancel it. The algebraic F action normalizes it to xi.

The relative projector can be assembled from the already constructed operations after the common finite level cover: degree projectors from multiplication by two; the neutral-weight projector from one fixed right-torus endomorphism; and the Tate projector from right-F pullbacks of a relative polarization and their constant dual intersection matrix. Squares span F over Q, so finitely many such divisors span its Tate subspace.

## What remains absent

There is still no uniform degree bound for the supports coming from the matched CM seed along its countable dense isogeny orbit. Density of that orbit does not give a repeated degree bound by pigeonhole: a countable union of finite sets can be dense.

The curve corollary sharpens this: if xi is not algebraic everywhere, each fixed-degree locus is finite. Along any sequence of distinct algebraic points, the minimum required support degree must tend to infinity. No numerical growth rate or actual degree bound is established.

The new test concerns the Mumford mixed class. Even a successful application would not prove F2 for all abelian varieties or F3' for arbitrary nonabelian varieties.

## Title and abstract

Suggested accurate title: **Algebraic Hodge Loci and Propagation from CM Fibres**.

Suggested brief abstract:

> We construct a matched CM fibre for a Mumford fourfold and an auxiliary abelian sixfold and prove algebraicity on all powers of the pair. We show that a uniform degree bound on supports with nonzero mixed projection would propagate the link to every fibre; bounded denominators follow automatically. An algebraic link at a full-group fibre gives all Hodge classes on powers of the Mumford fourfold. The required degree bound and the universal statements F2 and F3' remain open.

Do not use a resolution title. The proofs do not establish full F2 or F3'.

## Integration cautions

- The current full-paper introduction still says that no theorem produces the mixed cycle even at CM points. The new matched seed supersedes this blanket statement.
- Its older sixfold-link summary still imposes absence of an imaginary quadratic subfield. The new right-action transfer proof removes that condition.
- The abstract's blanket phrase about density in every family is broader than the explicit matched-Shimura/Weil-domain density arguments audited here. Name the relevant families unless a separate universal-density proof has been fully checked.
- A Chow/Hilbert component supplies flat cycle classes; it does not deform an arbitrarily chosen perfect complex. The semiregularity kernel remains a different obstruction.
- The existence-only denominator bound is not an effective numerical estimate for the actual Chow components. The appendix gives an explicit Cramer bound if class coordinates are already bounded; it does not supply the missing geometric degree bound.

The properness input is standard and supported by the [Stacks Project, Tag 01W0](https://stacks.math.columbia.edu/tag/01W0). Relative Chow spaces and cycle specialization are the same standard inputs used in the existing bounded-degree proposition and in Fulton's Intersection Theory. These refinements are not presented as new foundational theorems or as an independent proof of the Hodge conjecture.
