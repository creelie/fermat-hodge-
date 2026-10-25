# The F3′ reduction: what the correspondence construction proves

Write Hdgᵖ(X) for rational Hodge classes and Abᵖ(X) for the classes
Γ_*γ with Γ algebraic and γ a Hodge class on an abelian variety,
allowing sums and the point as a zero-dimensional abelian variety.

Let H_ab^(2p)(X) be the sum of images Γ_*Hᵏ(B), with the appropriate
degree shifts and Tate twists, where B is abelian and Γ is algebraic.
It is a rational sub-Hodge structure. Only finitely many images are
needed since the target is finite dimensional.

Take a direct sum of those finitely many source Hodge structures and
the resulting surjective morphism onto H_ab^(2p)(X). After Tate twists
all structures have the same weight. The category of rational
polarisable pure Hodge structures is semisimple, so the surjection
has a rational Hodge-theoretic section. A rational class of type (p,p)
in the target therefore lifts to a sum of rational classes of the
corresponding Hodge types in the sources. It follows that

    Abᵖ(X) = Hdgᵖ(X) ∩ H_ab^(2p)(X).

This supplies a precise argument for `prop:f3prime-known`(i) and
`prop:abpart`. There is no need to claim that each individual summand
of an invariant sum is invariant. The lift here is a morphism of Hodge
structures, not an assertion that a new algebraic correspondence
realising an arbitrary Hodge-theoretic splitting has been constructed.
The existing algebraic maps Γ_* are the ones used after taking the lift.

The global equivalence is then direct. If HC holds, every Hodge class
on X comes from the point using its representing cycle, so F3′ holds,
and AB holds as a special case. Conversely, AB makes each source γ in
F3′ algebraic, so Γ_*γ is algebraic by composition and pushforward.
Thus HC ⇔ (AB and F3′).

For an abelian X, F3′ holds without any conjectural input: take B = X
and the diagonal correspondence. It says nothing about whether the
source Hodge class itself has a cycle. For a general X, proving F3′
requires excluding rational Hodge classes in a Hodge complement to
H_ab^(2p)(X). Semisimplicity constructs the complement; it does not
show that the complement has no Hodge classes.

Consequently, constructing cycles for the two Mumford directions would
settle that particular AB instance, but would not by itself establish
F3′ for all varieties. The geometric generalisation remains unproved.
