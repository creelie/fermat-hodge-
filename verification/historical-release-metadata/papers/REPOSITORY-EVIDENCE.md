# Repository evidence and audit of the matched CM construction

This is a read-only mathematical audit of the cited repository content and of `paper/sixfold.tex`, `paper/seed.tex` and `paper/transfer.tex`. No repository theorem establishing F2 or F3′ was found. The matched CM seed is a valid special-fibre construction; its propagation to a full-group Mumford fibre is still an additional mathematical requirement.

## Checked repository evidence

The SHAs below are **Git blob SHAs**, not repository commit identifiers. They identify the exact file contents returned by the GitHub connector.

| File | Blob SHA | Exact short excerpt | What the file establishes |
| --- | --- | --- | --- |
| [eBLLM Hodge engine](https://github.com/creelie/eBLLM/blob/main/src/ebllm/bllm/hodge.py) | `3ee01df35114c19eb0205f3188bf438218df20c2` | “Nothing here proves an open statement unless its check does, and no check in this file does.” | Typed routes, finite calculations and explicit stopping rules. An accepted route does not construct the missing cycle or compute the missing deformation obstruction. |
| [Lean HodgeGap module](https://github.com/creelie/eBLLM/blob/main/lean/EBLLM/HodgeGap.lean) | `d6b6ec55dc41a00cc287a580a4fee05ea5f8dcf9` | “none of them is a statement about Hodge classes, and none proves (F2) or (F3').” | Finite arithmetic statements proved by `decide`, including obstruction-dimension comparisons and finite lists. These are not a formalization of cycle algebraicity or semiregular deformation. |
| [Hodge control record](https://github.com/creelie/eBLLM/blob/main/src/ebllm/controls/hodge.json) | `8eac97af5d57853dc537b981c8540a0bc9796960` | “Open. No candidate closure.” | Its proof and formalization factors are zero and `model_ok` is false. This is a status record, not independent evidence for a mathematical assertion. |
| [OpenGluon README](https://github.com/creelie/OpenGluon/blob/main/README.md) | `464d09616f654b61084d0d7793d69f1b768fc4db` | “Its result proves positivity of the supplied finite matrix.” | The exact rational checker verifies the supplied finite matrix. Pinned libraries, source inventories and route cards do not furnish an algebraic correspondence. |

The local OpenGluon Anaxia material inspected is a copy/pinned integration of the same engine, not an additional proof of F2 or F3′.

Two Hodge-engine conclusions are now too broad. First, its blanket vanishing of `Hom(X, Z_K)` even at CM points does not apply to the deliberately matched compositum seed below. Second, the Boolean condition in `link_closes`, excluding a field containing an imaginary quadratic subfield, is unnecessary for the new right-action transfer proof. These are limitations of the older route description, not proofs of general closure.

## Audit of the matched CM seed

**Field choice.** The construction of an imaginary quadratic field \(k\) with \(K=Fk\hookrightarrow D\) is sound. At a rational prime under a ramified place of the quaternion algebra, a completion of \(F\) of degree one or three cannot contain a quadratic extension of \(\mathbb Q_p\). At most one completion has degree two, and it forbids at most its own quadratic extension. Prescribing another local quadratic squareclass, together with a negative real squareclass, gives an imaginary quadratic \(k\) by weak approximation. The quadratic extension is a field at every ramified place of \(D\), which is precisely the local condition in the quadratic embedding criterion for a quaternion algebra. See Reiner, *Maximal Orders*, Section 32.

**Polarization.** For \(c\in K^-\), the alternating form

\[
\psi_c(x,y)=\operatorname{Tr}_{F/\mathbb Q}\operatorname{trd}(\bar xyc)
\]

is invariant under the left norm-one quaternion group and the right norm-one torus. At a compact real place, \(Jx=xj\) and \(c=-j\) give a positive multiple of the quaternion norm. At the split place, with \(j=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)\), \(Jx=jx\) and \(c=-j\), one obtains \(\operatorname{Tr}(x^{\mathsf t}x)>0\). Positivity persists under the left-group conjugation that varies the period. Multiplication of a fixed imaginary generator of \(k\) by an element of \(F\) permits the three required real signs independently. Thus the weight-one representation is polarizable; the sign choices do not invalidate the matched point.

**The graph is rational.** Put \(T=\operatorname{Res}_{F/\mathbb Q}\ker N_{K/F}\). The map

\[
q(t)=N_{K/k}(t)t^{-1}
\]

is a morphism over \(\mathbb Q\): the relative norm is a morphism of restriction-of-scalars tori and \(k\hookrightarrow K\) is rational. Moreover \(q(t)\overline{q(t)}=1\). On character coordinates it sends \(e_i\) to \(\sum_{j\ne i}e_j\), not to an independently chosen right character. At the matched Hodge circle this gives the right circles at the two compact places and the trivial right circle at the split place. The joint Hodge torus is therefore the graph of \(q\), rather than the product of independent left and right tori.

**Isogenies.** The eight weights of \(X_c\) are the sign triples. The pair \(\pm(1,1,1)\) is Galois-stable and gives a CM elliptic factor \(E\); the other six give a threefold \(B\). The weights on the three blocks of \(Z_c\) are \(\pm e_i\pm(e_j+e_\ell)\). They consist of three copies of the elliptic pair and one copy of the other six weights. The equality respects both Galois action and the Hodge circle, so

\[
X_c\sim E\times B,\qquad Z_c\sim E^3\times B\sim X_c\times E^2.
\]

**Algebraicity on all powers requires an extra argument, which the draft supplies.** Write the weights as \(\pm w_i\), where \(w_1=(1,1,1)\), \(w_2=(1,-1,-1)\), \(w_3=(-1,1,-1)\), \(w_4=(-1,-1,1)\). Their only relation is \(\sum_iw_i=0\). Removing opposite pairs from any zero-weight multiset leaves positive or negative tetrahedra. The tetrahedra define a rational \(k\)-action of Weil signature \((2,2)\). A \(k\)-compatible product polarization exists: for the action \(I^2=-d\), averaging \(\psi+d^{-1}I^*\psi\) retains positivity. Its Hermitian determinant \(\delta\) is a positive rational number. Rescaling the elliptic factor's polarization by \(\delta^{-1}\) makes this determinant one. Clearing denominators changes it by a rational fourth power, which is a norm from \(k\).

[Markman, JEMS 25 (2023), Theorem 1.5](https://ems.press/content/serial-article-files/32790?nt=1), journal page 236, proves algebraicity of the determinant space for **every** polarized Weil fourfold of discriminant one. The generic qualifier in the abstract concerns the resulting whole Hodge conjecture, not the determinant-space assertion of the theorem. This published result applies to the decomposable CM fourfold used here.

Opposite pairs are divisor classes. After a splitting extension, the Hodge endomorphism algebra of \(H^1(X_c)\) is diagonal on its eight distinct torus weights. Pullbacks under rational homomorphisms \(X_c^m\to X_c\), followed by polynomial polarization in their endomorphism parameters, span the pairs and tetrahedra in arbitrary slots. Rational points are Zariski dense in that parameter vector space. Products then span every invariant. Scalar extension of the rational cycle-class image is faithful, so the conclusion descends to rational coefficients. The isogeny retract \(Z_c\sim X_c\times E^2\) gives algebraicity on every \(X_c^a\times Z_c^b\), including the mixed class \(\xi_c\).

No mathematical error was found in this seed argument after checking these descent and polarization details. This audit does not establish its priority or novelty.

## Why the seed does not prove F2 or F3′

At a full-group Mumford fibre, \(H^1(X)\) is the tensor product of all three standard representations, whereas the sixfold representation is a sum supported at individual factors. There is then no nonzero Hodge homomorphism \(H^1(X)\to H^1(Z)\). The CM isogeny retract therefore does not extend as the same homomorphism to the generic fibre.

The algebraic right action on \(T_Z\) and the transfer argument are valid **if a nonzero algebraic mixed link exists at a full-group fibre**. Polynomial inversion of \(f^\dagger f\) constructs the projector and transports the \(F\)-action. Partial symplectic transpose and independent factor swaps then generate the invariant tensors. The missing assertion is the premise: neither the repository checks nor the CM representative prove deformation of that representative through the family.

## Pure Chern characters do not remove the obstruction

Let \(Y=X_c^2\times Z_c\), of dimension 14, and let \(h\) be a product ample class. The mixed Künneth degrees of \(\xi_c\) are \((1,1,2)\), hence \(\int_Y\xi_c h^{12}=0\).

1. There is no coherent sheaf with **total** Chern character \(N\xi_c\ne0\). Such a sheaf has rank zero. Its first nonzero Chern-character component is the effective fundamental cycle of its largest-dimensional support, with positive intersection against the corresponding ample power. A pure degree-four character would therefore have positive \(h^{12}\)-degree, contradicting the displayed equality. This is the leading-support formula for the Chern character; see Fulton, *Intersection Theory*, Section 18.3.
2. There is no slope-stable locally free bundle with total character \(r+N\xi_c\ne r\). It has \(c_1=0\) and \(c_2h^{12}=0\). The Hermitian–Einstein curvature identity forces its curvature to vanish, so its positive-degree Chern character vanishes. The existence input is [Uhlenbeck–Yau (1986)](https://doi.org/10.1002/cpa.3160390714).
3. These arguments do **not** exclude a perfect complex, an arbitrary coherent sheaf with total character \(r+N\xi_c\), or a sheaf with only its second character prescribed. These distinctions must be preserved.
4. Adams operations isolate a rational \(K_0\)-class and a perfect-complex representative, but do not establish semiregularity. For a direct sum the Atiyah class is block diagonal, so every semiregularity component vanishes on the off-diagonal \(\operatorname{Ext}^2\) summands. For \(E\oplus E\) it vanishes on \(\operatorname{Ext}^2(E,E)\otimes\mathfrak{sl}_2\). Additivity therefore supplies no injectivity theorem. The comparison between the obstruction and its semiregularity image is an obstruction theorem, not the vanishing of its kernel; see [Pridham, Forum of Mathematics Sigma (2024)](https://doi.org/10.1017/fms.2024.132).

The strongest verified conclusion is an algebraic mixed class at a matched CM fibre and an explicit conditional transfer at full-group fibres. An algebraic representative whose relative deformation space dominates the Mumford curve, or another actual construction of the generic mixed cycle, is still required.
