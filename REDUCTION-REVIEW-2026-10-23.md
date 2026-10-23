# Reduction proof corrections, 23 October 2026

This revision proves neither F2 nor F3-prime. It constructs no algebraic
representatives of the two exceptional Mumford classes. The conjecture remains
open in this work.

In `paper/sec3_reduction.tex`, the proof that F2 implies the Hodge conjecture
for abelian varieties is repaired by separating the cases beta outside R(A)
and beta in R(A). In the latter case the symplectic group fixes beta, so a
group element moving a primitive exceptional class e moves beta tensor e.
Hodge--Riemann gives the nonzero rational contraction

    q = integral_(X x X) e e theta^4 > 0.

Both needed algebraic classes are supplied explicitly by the hypothesis F2;
their product and pushforward recover beta after division by q, with the displayed normalization
in the manuscript. The earlier inference from ge = +/-e to a contradiction
after squaring g is removed. The exceptional endomorphisms concern H^2(X),
not H^1(X).

The proof of F3-prime for the class A uses a rational Hodge splitting of the
whole correspondence surjection. It no longer asserts that the individual
terms of an arbitrary lift are Hodge classes.

`code/mumford_dimension_check.py` uses exact integer weight multiplicities and
rational exterior algebra. It gives degree-four Kunneth invariant dimensions
1, 1, 4, 1, 1; total 8; divisor-product rank 6; quotient dimension 2. This is
a representation calculation, not a cycle construction or a formal Lean
proof of the analytic or geometric assertions.

Blowing up does not automatically remove a missing algebraic representative:
for a blowup pi of smooth projective varieties, pi_* pi^* alpha = alpha and
proper pushforward preserves algebraic cycle classes. Thus algebraicity of
pi^* alpha implies algebraicity of alpha. For a generically finite proper map
of degree d the corresponding identity is f_* f^* alpha = d alpha.

The full manuscript compiles, with the corrections, in the journal format.
Other proofs and external dependencies of the full paper have not all been
independently checked by this revision.
