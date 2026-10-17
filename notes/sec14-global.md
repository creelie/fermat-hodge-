# Section 14, global step for 6 | M

Status marks as in `even-degrees.md`: **proved**, **checked** (script named),
**open**.

## G0. Setting

M is divisible by 6 and 110 ∤ M. A is a sextuple at level M (balanced, no
pair, generates Z/M, not split). For a ∈ A, f(a) is the prime-to-6 part of its
order. E is the set of the values f(a) that are maximal for divisibility. For
e' ∈ E, B_{e'} = {a ∈ A : f(a) = e'}; the other elements form the low part L.
D'(e') is the 2,3-part of the lcm of the orders in B_{e'}, so B_{e'} lies in
the subgroup of order D'(e')e'.

The local step (files `sec14-reduction.md`, `sec14-prime.md`,
`sec14-composite.md`) says: the relations eq:charrel at conductors whose
prime-to-6 part is e' involve only B_{e'}; a chain of moves for B_{e'} at
level D'e' (T(x), sigma_{l,x}, ending in at least two fewer elements or in a
lower top) is a chain for A; and the configurations B_{e'} without such a
chain are, up to units, those of the following list (**checked** with
`m6/locD.c`, `m6/lchain.py`, `glob/residuals.py` at 2-parts up to 16 and
3-parts up to 27 of D' for e' = 5, 7, 11, 13, 17, 19, and at fewer levels for
23 ≤ e' ≤ 143; the hand proof is the content of the three local files):

| e' | sizes | D' |
|---|---|---|
| 5 | 2, 3, 4, 5, 6 | 3, 4, 6, 8, 12, 18, 24 |
| 7 | 3, 4, 5, 6 | 3, 4, 6, 8, 12, 24 |
| 11 | 3, 4, 5, 6 | 4, 6 |
| 13 | 3, 4, 6 | 6 |
| 17, 19 | 6 | 6 |
| 35 | 4, 5 | 2 |
| 35 | 6 | 1, 2, 3, 6 |
| 55 | 5, 6 | 2 |

No other e' carries one. At e' = 35 the residual of size 4 is {1, 24, 61, 62}
at level 70, and those of size 5 are {1, 4, 32, 44, 62} and
{1, 24, 44, 52, 62}.

Below: if A has no chain, then each B_{e'} is in the list.

## G1. Invariance under the units fixing the high part (proved)

**Lemma.** Let A' ⊆ A, N the lcm of the orders of the elements of A - A', and
W = {w ∈ (Z/M)^x : w ≡ 1 mod N}. Then s(t) = Σ_{a ∈ A'} ⟨ta/M⟩ satisfies
s(tw) = s(t) for all units t and all w ∈ W.

Proof. w fixes every element of A - A', and Σ_{a ∈ A} ⟨ta/M⟩ = 3 for every
unit t. ∎

**Corollary (one low element).** If A' = {a}, then M | lcm(N, 2).

Proof. W maps onto the kernel of (Z/n)^x → (Z/g)^x, n = ord(a),
g = gcd(n, N) (Chinese remainder theorem, M = lcm(N, n)). If this kernel is
not trivial, then twa ≠ ta for some w, and ⟨twa/M⟩ ≠ ⟨ta/M⟩. The kernel is
trivial only for n = g or n = 2g with g odd, and then M = lcm(N, n) divides
lcm(N, 2). ∎

## G2. One maximal part (proved, given the list)

Let E = {e'}. Every f(a) divides e', so M = 2^a 3^b e'.

* e' = 1, 5, 7: M = 2^a 3^b 5 or 2^a 3^b 7, Aoki [Aok00].
* e' = 11, 13: e84hc Theorem A (2^a 3^b 11^c and 2^a 3^b 13^c).
* e' = 17, 19: the residual has six elements, so A = B_{e'}, M = 6e' = 102 or
  114, e84hc Theorem A (2^a 3^b 17^c and 2^a 3^b 19^c with a ≤ 1).
* e' = 55: 110 | M, excluded.
* e' = 35: G3.
* any other e': no residual, so A has a chain.

## G3. The part 35 (proved, given the list)

Let E = {35} and 6 | M. Write M = 35C, C the 2,3-part (6 | C).

* |B| = 6: A = B lies in the subgroup of order 35D' with D' | 6, so M = 210.
* |B| = 5: D' = 2, so N = 70 in G1 and M | 70, against 3 | M.
* |B| = 4: B = u{1, 24, 61, 62} at level 70 for a unit u, and
  L = {a_1, a_2}. Write a_i/M ≡ α_i/C + γ_i (mod 1), α_i ∈ Z/C,
  γ_i ∈ (1/35)Z/Z of denominator f_i ∈ {1, 5, 7}. By G1 with A' = L and
  N = 70, W ≅ (Z/C)^x acts on the α_i alone and s(t) = ⟨ta_1/M⟩ + ⟨ta_2/M⟩
  is W-invariant.
  - If exactly one α_i has order > 2, s is not W-invariant (as in the
    corollary). If both have order ≤ 2, then C | 2, against 3 | C. So both
    have order > 2.
  - Modulo 1, s(tw) - s(t) ≡ t(w - 1)(α_1 + α_2)/C; with w = -1,
    2(α_1 + α_2) ≡ 0 mod C, so α_2 = -α_1 + δC with δ ∈ {0, 1/2}.
  - {f_1, f_2} ≠ {5, 7}: if 3 divided α_1, it would divide α_2 = -α_1 + δC,
    and lcm(2, ord α_1, ord α_2) would miss the 3-part of C; so 3 divides
    both orders. At conductor 3 only a_1, a_2 enter eq:charrel (the elements
    of B have orders dividing 70), with weights
    ±(1 - χ_3(2))^{[2 | ord α_i]} w(f_i) / φ(ord a_i), w(1) = 1,
    w(5) = 1 - χ_3(5) = 2, w(7) = 1 - χ_3(7) = 0. For {f_1, f_2} = {5, 7}
    exactly one weight vanishes, and the relation fails.
  - For every t, {u + x} + {κ - u - x} ∈ {κ, κ + 1}, so
    s(t) ≡ δ + t(γ_1 + γ_2) (mod 1), a fraction whose denominator divides
    2 lcm(f_1, f_2), hence 10 or 14. At t = u^{-1}: h(tB) =
    (1 + 24 + 61 + 62)/70 = 148/70, so s(t) = 3 - 148/70 ≡ 31/35, of
    denominator 35. Contradiction.

So for 6 | M the part 35 occurs only at M = 210 with A = B (four sextuples
up to units, none with a splitting or a 4-tuple move; `glob/extra.py`). The
Hodge conjecture for X^4_210 follows from Aoki's reduction (Q(210) = {15, 21,
35}) and the class ξ_35.

**ξ_35 without Peterson's coniveau computation (proved by hand).** The
character α = (1, 2, 16, 21, 30) of μ_35^5, the one Peterson uses, admits a
block pattern in the sense of e84hc def:blockpattern: columns
(0,0,0,5,0), (1,1,2,0,0), (1,2,0,0,1), (3,1,0,0,1), (0,0,0,0,35) with
δ = 10, 25, 10, 5, 1. The weights are 105, 35, 35, 35, 1050 (all divisible by
35), every coordinate sum is D = 50, and Σδ = 51 > D. So by e84hc
thm:uniruled, M_α ⊆ N^1 H^3(X^3_35). With the curve character
b = (17, 22, 31) one has ⟨tα⟩ + ⟨tb⟩ = 4 for every unit t, so by e84hc
prop:joindivisor(b) the eight-element multiset
β = {1, 2, 16, 17, 21, 22, 30, 31} is balanced and algebraic. Its only
element with square 1 mod 35 is 1, so ν_R([β]) = 1 (e84hc lem:nusqrt,
35 = 5·7), and as Q(35) = {35}, the argument of e84hc cor:B114 gives
B_35 = S_35 + Z[β]: the Hodge conjecture for X^n_35 in every dimension,
and so ξ_35. This replaces [Pet26] (whose character it is) by the e84hc
uniruled-quotient step. b is the only curve character with this property
(search in `bp/`; the block pattern from `bp/bp.py`, LP value 1.02).

## G4. Two maximal parts (proved, given the list; the final count checked)

The minimal sizes are 2 (5), 3 (7, 11, 13), 4 (35), 5 (55), 6 (17, 19). Two
maximal parts e_1, e_2 are incomparable, so with |B_1| + |B_2| ≤ 6 and
110 ∤ M the pairs are {5, 7}, {5, 13}, {7, 11}, {7, 13}, {11, 13}, and at most
one element is low. Three maximal parts would need at least 2 + 3 + 3 = 8
elements.

**Bound.** With Λ = lcm(D'_1, D'_2), the high part has lcm Λ e_1 e_2, so by
the corollary of G1, M ∈ {Λ e_1 e_2, 2Λ e_1 e_2}, the second only when Λ is
odd and one element is low; if Λ is odd and no element is low, M is odd
(e84hc Theorem B).

**Finite check** (`glob/twopart.py`, `glob/extra.py`): over all pairs of
residuals, all unit twists of the second and the forced low element, the
balanced sextuples with no pair that generate Z/M and are not split are:

* {5, 7}: 24, at M = 210 and 420;
* {5, 13}: 7, at M = 390 and 780;
* {7, 13}: 6, at M = 546;
* {7, 11}, {11, 13}: none.

All 37 are of the form Q_1 + Q_2 - {t, -t} with Q_1 = {a, b, c, -t},
Q_2 = {t, d, e, f} balanced 4-tuples, t ∈ {M/4, M/2, 3M/4}; balanced 4-tuples
are algebraic (Lefschetz (1,1)), so all 37 are algebraic. The degrees 210 and
420 also follow from Aoki and Peterson except at 420; 390, 780 and 546 are
not covered by known theorems, and need the splitting.

Examples: at 390, {5, 13, 260, 275, 305, 312} = {5, 275, 305, 195} +
{13, 260, 312, 195} - {195, 195}; at 546, {7, 13, 312, 385, 427, 494} =
{7, 385, 427, 273} + {13, 312, 494, 273} - {273, 273}; at 420,
{7, 45, 175, 285, 343, 405} = {7, 175, 343, 315} + {45, 285, 405, 105} -
{105, 315}.

## G5. Conclusion

**Theorem (given the local list).** Let 6 | M, 110 ∤ M. Every sextuple at
level M either has a chain of moves to at most four elements, to six elements
of lower profile or lower level, or to a split sextuple; or it is a sum of two
balanced 4-tuples minus a pair; or M is a degree at which the Hodge
conjecture follows from Aoki's reduction and the classes ξ_q, q in {12, 15,
20, 21, 28} (Aoki), {33, 39, 44, 51, 52, 57} (e84hc Theorem A) and 35 (G3). With Section 13 and
e84hc Theorem B, by induction on (M, profile), the Hodge conjecture holds for
X^4_M whenever 110 ∤ M.

What this rests on: the local list of G0. Its proof by hand for all D' and
all e' is the open part (the three local files); the computation covers
only the levels named in G0.
