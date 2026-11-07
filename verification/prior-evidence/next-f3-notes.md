# F3-prime geometric-transfer audit

Date: 7 November 2026.
Proposal: `next-f3-proof.tex`. No manuscript files were edited.

## What the existing manuscript already proves

- `main.tex`, Proposition `prop:bypass` (ii): blow-up decomposition
  for Hodge classes modulo algebraic classes.
- `main.tex`, Proposition `prop:surgery` (i): injectivity of both
  defects under generically finite surjective morphisms.
- `v7-bypass-audit.tex`, Proposition `v7:rational-varieties`:
  universal F3-prime for rational varieties already has the force of
  universal F3-prime, by placing an arbitrary variety in a blow-up
  centre. The same is true for the rational Hodge conjecture.

## Additional exact constructions

The proposed text makes the following standard consequences explicit.
No independent novelty claim is justified by this audit.

1. The **F3-prime defect has the full projective-bundle and blow-up
   direct-sum formulas**, not only a monotonicity inequality. The
   projective-bundle inverse is triangular and uses pushforwards of
   powers of the hyperplane class. The exceptional part of a blow-up
   is extracted by this inverse after restriction to the exceptional
   divisor and the self-intersection formula.
2. A generically finite morphism gives a **trace projector**, so the
   defect upstairs splits into the injected original defect and a
   trace-zero complement. For a smooth finite group quotient, the
   defect downstairs is exactly the invariant part of the defect
   upstairs. Passing to a cover cannot remove the pulled-back class.
3. The codimension-two defect is **stable birationally invariant**.
   The codimension `dimension minus two` defect enjoys the analogous
   assertion with its index shifted under stabilization. The latter
   extends the boundary case written as `dimension minus one` in the
   current surgery proposition, where the defect is already zero.
   These are classical consequences, not solutions of the unknown
   codimension-two case in general.
4. A **fully explicit algebraic projector on Hodge classes in degree
   four** removes the nonprimitive divisor summand. Its coefficients
   are the inverse of the divisor intersection matrix

   `Q[i,j] = integral D[i] D[j] h^(d-2)`.

   It sends a class `alpha` to

   `h * sum D[i] Q_inverse[i,j] integral alpha D[j] h^(d-3)`.

   The Hodge index theorem proves the matrix is invertible. Hard
   Lefschetz shows that the complementary map is the primitive
   projection **on rational Hodge classes**. The explicit cycle
   formula proves this needs no algebraicity assumption on a general
   inverse Lefschetz operator. Composing every abelian-source
   correspondence with the complementary projector reduces F3-prime
   in degree four exactly to its primitive part.

## Limits and safeguards

- The last projector is not the full primitive projector on all of
  `H^4`. It removes `h Hdg^1`, not the generally larger `h H^2`.
- It removes an already algebraic part. It does not prove that the
  remaining primitive quotient vanishes.
- The blow-up formula transports the primitive obstruction into a
  direct summand; it does not destroy it. An arbitrary variety used
  as the centre places that same unknown class in the new variety.
- For a finite group quotient, only defect representations with no
  invariant component disappear. A class pulled back from the
  quotient is invariant and cannot disappear this way.
- The low-dimensional corollary is consistent with the rational
  Hodge conjecture for smooth projective stably rational varieties
  of dimension at most five. It does not extend that result to all
  higher-dimensional rational varieties.
- These constructions do not prove F2 or universal F3-prime.

## Primary-source checks

- Yu. I. Manin, *Correspondences, motifs and monoidal transformations*,
  Math. USSR-Sb. 6 (1968), 439-470, especially sections 7 and 9.
  DOI: https://doi.org/10.1070/SM1968v006n04ABEH001070.
  Authoritative article record and English PDF:
  https://www.mathnet.ru/eng/sm4066.
  These supply the correspondence decompositions used here.
- The Stacks Project, projective-space bundle formula, Tag 0FGP:
  https://stacks.math.columbia.edu/tag/0FGP.
  Pullback and projection formula, Tag 0B2X:
  https://stacks.math.columbia.edu/tag/0B2X.
- D. Abramovich, K. Karu, K. Matsuki, J. Wlodarczyk,
  *Torification and factorization of birational maps*,
  J. Amer. Math. Soc. 15 (2002), 531-572, Theorem 0.1.1.
  Author-hosted journal article:
  https://personal.math.ubc.ca/~karu/papers/semist.pdf.
  DOI: https://doi.org/10.1090/S0894-0347-02-00396-X.

The proposed LaTeX uses the manuscript's existing `Man68` and
`AKMW02` bibliography entries. Hodge index, hard Lefschetz and
Lefschetz (1,1) are classical structural inputs, rather than new
unproved assumptions.
