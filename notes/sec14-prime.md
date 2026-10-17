# Section 14, local step at a prime e' = p

Status marks as in `even-degrees.md`: **proved**, **checked** (script named),
**open**. The scripts and their outputs are in `scratch-checks/forkB/` (with
`m6/locD.c` and `m6/lchain.py` of the parent); `README.txt` there lists them.

## Q0. Statement

p ≥ 5 is a prime, D = 2^v 3^w with v ≤ 3, w ≤ 2, N = Dp. A local configuration
at level N is, as in `m6/locD.c`, a multiset B of 1 to 6 elements x ∈ Z/N with
p ∤ x such that the p-primitive part of t ↦ Σ_{x∈B} ⟨tx/N⟩ vanishes, with no
pair {x, -x}, no T-pair {x, x + N/2}, no two distinct elements of one order e,
3 | e ≠ 3, in one coset x + (N/3)Z, and no (p+1)/2 distinct elements of one
order e ≠ p in one coset x + (N/p)Z. D_B is the 2,3-part of the lcm of the
orders in B and L_B = lcm(D_B, 6); B lies in the subgroup of order L_B p.

A local chain is a chain of moves in the sense of `m6/lchain.py`: at most two
moves, each adding one of the balanced sets T(x) = {x, x + N/2, -2x, N/2},
σ_{3,x} = {x, x + N/3, x + 2N/3, -3x}, σ_{p,x} (with the anchors of
`lchain.py`, removing the elements it hits, adding the negatives of the others
and cancelling pairs), ending in at least two fewer elements or in a lower top.
Chains are searched at level L_B p. Since 6 | M and D_B p | M in G0 of
`sec14-global.md`, L_B p | M and a move at level L_B p is a move at level M.
(G0 says level D'e'; the two agree when 6 | D_B, and for p ≤ 19 the
configurations without a chain are the same at level L_B p as at level 72p,
Q7(c).)

Multiplication by 72/D embeds level Dp into level 72p, preserving the
condition, the filters, the orders and L_B, so it suffices to treat D = 72;
the lists below are given by D_B.

**Theorem P.** Let D | 72.

(i) For every prime p ≥ 23, every local configuration at level Dp has a local
chain.

(ii) For p = 5, 7, 11, 13, 17, 19 the configurations at level Dp without a
local chain are, up to units, those of Q8 with D_B | D: 82, 27, 11, 9, 3 and
3 configurations at D = 72. Their D_B and sizes are those of the table of
`sec14-global.md` for D_B | 72.

The proof splits along

  P_exc = {5, 7, 11, 13, 17, 19, 23} ∪ P_cand,
  P_cand = {p ≥ 29 prime : 2^a 3^b ≡ ±1 mod p for some |a| ≤ 18, |b| ≤ 12,
            (a, b) ≠ (0, 0)}
         = {p ≥ 29 prime : p | 2^a 3^b ± 1 or p | 2^a ± 3^b, 0 ≤ a ≤ 18,
            0 ≤ b ≤ 12, (a, b) ≠ (0, 0)},

594 primes from 29 to 69657034753 (`cand.py 18 12`, list `Pcand.txt`), so
|P_exc| = 601. Every prime from 29 to 523 is in P_cand; the least primes
outside are 541, 739, 773, 859.

* For p ∉ P_exc, (i) is **proved** by hand (Q1 to Q3, Q6) from one finite
  computation that does not depend on p: the formal list of Q5 and its chains
  (**checked**, `prop V W 0`, `fchain.py`), produced by a search whose
  completeness is proved (Q4).
* For p ∈ P_exc, (i) and (ii) are **checked** directly (Q7).

## Q1. The relations as point conditions (proved)

Write x ∈ Z/N with p ∤ x as x ↔ (s, u), s = x mod D, u = x mod p ≠ 0, and
put g = gcd(s, D) (g = D for s = 0), d = D/g (so ord x = dp), r = s/g, a unit
mod d. The p-primitive part of f(t) = Σ_{x∈B} ⟨tx/N⟩ vanishes iff
Σ_t f(t) χ̄(t) = 0 for every character χ = ψφ of (Z/N)^x with φ ≠ 1 (φ mod p,
ψ mod D). For x = g x', ⟨tx/N⟩ = ⟨tx'/(dp)⟩, the sum over t vanishes unless
χ is defined mod dp, and then equals
(φ(N)/φ(dp)) · dp · χ(x') · B_{1,χ̄*} · Π_{ℓ | dp, ℓ ∤ cp} (1 - χ̄*(ℓ)),
with χ* primitive of conductor cp (c the conductor of ψ, c | D) and
B_{1,χ̄*} ≠ 0 for odd χ; for even χ the sum is 0. So B is a configuration iff,
for every c | D with c ≢ 2 mod 4, every primitive ψ mod c and every φ ≠ 1 with
ψφ odd,

  Σ_{x : c | d_x} (1/φ(d_x)) Σ_{T ⊆ L_x(c)} (-1)^{|T|} ψ(r_x/ΠT) φ(u_x/(g_x ΠT)) = 0,   (Q1.1)

L_x(c) = {ℓ ∈ {2,3} : ℓ | d_x, ℓ ∤ c} (this is eq:charrel). Let
ν_c(r, v) = Σ_{x : c | d_x} (φ(D)/φ(d_x)) Σ_T (-1)^{|T|} [r = r_x/ΠT mod c][v = u_x/(g_x ΠT)],
a function on (Z/c)^x × (Z/p)^x with integer values, and
μ_ψ(v) = Σ_r ψ(r) ν_c(r, v). (Q1.1) for all φ ≠ 1 with φ(-1) = -ψ(-1) says:
μ_ψ(-v) = μ_ψ(v) for all v when ψ is even, and μ_ψ(v) + μ_ψ(-v) = κ_ψ (a
constant) when ψ is odd. With ω_c(r, v) = ν_c(r, -v) - ν_c(-r, v) one has
Σ_r ψ(r) ω_c(r, v) = μ_ψ(-v) - ψ(-1) μ_ψ(v), and
P_c = Π_{ℓ | c} (|K_ℓ| - Σ_{k ∈ K_ℓ} R_k), K_ℓ = ker((Z/c)^x → (Z/(c/ℓ))^x),
R_k the translation by k, multiplies a character ψ of (Z/c)^x by Π|K_ℓ| if ψ
is primitive and kills it otherwise. Hence, when every κ_ψ = 0, B is a
configuration iff

  P_c ω_c(·, v) = 0 for every layer c and every v ∈ (Z/p)^x.                 (Q1.2)

The layers are c ∈ {1, 3, 4, 8, 9, 12, 24, 36, 72} ∩ {c | D}. (Q1.2) only
compares values at v and -v, so it is a condition at each point (c, {±v}); an
element x meets the points (c, ±u_x/(g_x ΠT)), c | d_x, T ⊆ L_x(c), at most 16
of them. The residual of B at a point is the vector P_c ω_c(·, v) there; it is
additive in B.

## Q2. The constants vanish for p ≥ 29 (proved)

If κ_ψ ≠ 0 then v or -v lies in the support of μ_ψ for every v, so the support
has at least (p-1)/2 points. For odd ψ the conductor c is one of 3, 4, 8, 9,
24, 72 (and 36 for D = 36, 72), and a single element puts at most
2^{|L_x(c)|} ≤ 2 masses into ν_c (|L_x(c)| ≤ 1 since 2 | c or 3 | c), so the
support has at most 12 points. Thus κ_ψ = 0 when (p-1)/2 > 12, i.e. p ≥ 29,
and for p ≥ 29 (Q1.2) is equivalent to the configuration condition. (At p = 23
the bound fails, and the configurations there are enumerated with locD, Q7(b).)

## Q3. Components and the formal regime (proved)

Two elements touch if they meet a common point (c, {±v}). Let p ≥ 29. The
residual of B at a point is the sum of the contributions of the elements
meeting it, and these lie in one component of the touch graph; so each
component of a configuration satisfies (Q1.2). The filters forbid certain
sub-multisets, so they pass to sub-multisets. Hence every component of a
configuration is a configuration, and a minimal configuration (no proper
sub-multiset is a configuration) is connected.

In a connected configuration all u lie in one coset u_0 ⟨-1, 2, 3⟩ ⊆ (Z/p)^x,
since touching elements have u_y/u_x = ±o_y/o_x with offsets o = g ΠT =
2^α 3^β dividing D. Multiplying by a unit of Z/N we may take u_0 = 1 and one
element of largest order equal to x_0 = (D/d_0, 1).

The formal regime replaces ⟨-1, 2, 3⟩ ⊆ (Z/p)^x by the free group
G = {±1} × Z^2 (u = ±2^a 3^b formally) and imposes (Q1.2) and the filters in
G. Reduction G → (Z/p)^x is a homomorphism, and the residual of the reduction
at a point is the sum of the formal residuals at the points above it; so a
formal configuration reduces modulo every p ≥ 5 to a multiset satisfying
(Q1.2) with all κ_ψ = 0, which is a configuration whenever the filters still
hold.

## Q4. The propagation search (proved complete; checked against locD)

Let p ≥ 29 (or the formal regime), S a connected configuration containing the
base x_0 = (D/d_0, 1), an element of largest order, and C ⊆ S a sub-multiset
containing x_0. If the residual of C is not zero at a point π, then S - C
contains an element meeting π, since the residual of S at π is zero. The
covers of π = (c, {±v}) are the elements (s, ±v o) with c | d_s and o an
offset of s in layer c. `prop.c` starts from C = {x_0}, takes a point π with
nonzero residual and fewest covers, and branches over the covers y_1, ..., y_m
that pass the filters together with C, the i-th branch adding y_i and
excluding y_1, ..., y_{i-1} from the rest of the branch (repetitions of y_i
stay allowed); it stops at residual zero or at 6 elements, and prunes when a
layer has more nonzero points than the remaining slots times the largest
number of points an element meets in that layer. Elements of order larger
than ord x_0 are not added. Following, at each node, the first cover lying in
S - C shows that every S ∋ x_0 with no proper sub-configuration containing x_0
is reached, in particular every minimal configuration. The output is taken up
to units (lex-min over the choice of base element and the units of Z/D fixing
it).

Checks:

* `prop` modulo p against `locDm` (= `m6/locD.c` with the table split into K
  hash classes, same output) and `cmp.py` (same lists up to units of Z/N;
  every locD configuration outside the prop list decomposes into prop ones):
  p = 29, 31, 37, 41, 43 at D = 6 and 12; p = 29, 31, 37 at D = 18;
  p = 29 at D = 24, 36 and 72 (8 to 16 configurations each, all equal;
  `X_2_2_29.txt`, `X_3_2_29.txt` for D = 36, 72).
* At the primes 541 and 739 outside P_exc, Q7(d).
* `fchain.py` (the moves T and σ_3 of `lchain.py` in CRT coordinates, formal
  or modulo p) agrees with `lchain.py` on 560 random multisets at
  Dp = 6·29, 12·31, 72·29 (`randtest.py`: the same multisets have no chain).

## Q5. The formal list (checked: `prop V W 0`, `fchain.py 72 0 2`)

The search of Q4 in the formal regime ends (1048885 nodes at D = 72) with 16
configurations at D = 72 (`F_3_2.txt`), none at D ∈ {1, 2, 3, 4, 8, 9}, 8 at
D = 6 and 18, 12 at D = 12 and 36, 16 at D = 24: by D_B, 8 with D_B = 6, 4
with D_B = 12 and 4 with D_B = 24; 4 of size 5 and 12 of size 6. Every one has
a local chain (`FC_3_2.txt` at level 72, `fdump/` at level L_B).

Below, at level L_B: an entry s:ε,a,b is the element x ≡ s mod L_B,
x ≡ ε 2^a 3^b mod p; 0,0,0 means x ≡ 0 mod p. After | the moves of the chain,
written T(y) or s3(y) with the anchor y of `lchain.py`, and the multiset after
each move.

L_B = 6:

    0:-1,-1,1 0:1,-1,0 2:1,-1,0 2:1,0,0 5:-1,-1,0
      | s3(0:1,-1,0) -> 2:-1,-1,0 2:1,0,0 5:-1,-1,0
    0:-1,-1,1 0:1,0,0 1:-1,-1,0 3:-1,-1,0 4:1,-1,0 4:1,0,0
      | T(0:-1,-1,0) -> 0:-1,-1,1 0:1,-1,0 1:-1,-1,0 3:0,0,0 4:1,-1,0 4:1,0,0
    0:-1,-1,-1 0:1,0,0 1:1,-1,-1 3:-1,-1,0 4:-1,-1,-1 4:-1,0,-1
      | T(0:-1,-1,0) -> 0:-1,-1,-1 0:1,-1,0 1:1,-1,-1 3:0,0,0 4:-1,-1,-1 4:-1,0,-1
    1:-1,0,-1 2:-1,2,-1 3:-1,0,-1 3:1,0,0 4:1,0,-1 5:1,1,-1
      | s3(1:-1,0,-1) -> 1:1,0,-1 2:-1,2,-1 4:1,0,-1 5:1,1,-1
    0:-1,-2,1 0:1,-2,0 1:-1,-2,0 2:1,0,0 4:1,-2,0 5:-1,-1,0
      | s3(0:1,-2,0) -> 1:-1,-2,0 2:1,0,0 4:-1,-2,0 5:-1,-1,0
    0:-1,-1,0 0:1,0,0 1:-1,-1,-1 3:-1,-1,-1 4:-1,0,-1 4:1,-1,-1
      | T(0:-1,-1,0) -> 1:-1,-1,-1 3:-1,-1,-1 3:0,0,0 3:1,-1,0 4:-1,0,-1 4:1,-1,-1
      ; T(1:-1,-1,-1) -> 2:-1,0,-1 2:1,-1,-1 3:-1,-1,-1 3:1,-1,0 4:-1,0,-1 4:1,-1,-1
    0:-1,-1,0 0:1,0,0 1:1,-1,0 3:-1,-1,1 4:-1,-1,0 4:1,0,0
      | T(0:-1,-1,0) -> 1:1,-1,0 3:-1,-1,1 3:0,0,0 3:1,-1,0 4:-1,-1,0 4:1,0,0
      ; T(1:1,-1,0) -> 2:-1,-1,0 2:1,0,0 3:-1,-1,1 3:1,-1,0 4:-1,-1,0 4:1,0,0
    1:-1,0,-1 3:-1,0,-1 3:1,0,0 4:-1,1,-1 4:1,0,-1
      | s3(1:-1,0,-1) -> 1:1,0,-1 4:-1,1,-1 4:1,0,-1

L_B = 12:

    1:-1,-1,-1 1:1,-1,-1 6:1,0,0 9:-1,-1,-1 9:-1,-1,0 10:-1,0,-1
      | T(1:1,-1,-1) -> 1:-1,-1,-1 5:-1,-1,-1 6:0,0,0 6:1,0,0 9:-1,-1,-1 9:-1,-1,0
    1:-1,-1,0 1:1,-1,0 6:1,0,0 9:-1,-1,0 9:-1,-1,1 10:1,0,0
      | T(1:-1,-1,0) -> 1:1,-1,0 5:1,-1,0 6:0,0,0 6:1,0,0 9:-1,-1,0 9:-1,-1,1
    1:-1,0,0 1:1,0,0 8:-1,1,0 8:1,2,0 9:-1,0,1 9:1,0,0
      | s3(1:1,0,0) -> 1:-1,0,0 7:-1,0,0 8:-1,1,0 8:1,2,0
    1:-1,0,0 1:1,0,0 9:-1,0,0 9:1,0,1 10:-1,1,0
      | s3(1:-1,0,0) -> 1:1,0,0 7:1,0,0 10:-1,1,0

L_B = 24:

    1:-1,-1,0 2:1,0,0 9:-1,-1,0 19:1,-1,0 20:-1,1,0 21:1,-1,1
      | s3(1:-1,-1,0) -> 2:1,0,0 7:1,-1,0 19:1,-1,0 20:-1,1,0
    1:-1,0,0 3:1,0,0 6:-1,1,1 19:1,0,0 21:1,0,1 22:1,1,0
      | T(1:-1,0,0) -> 3:1,0,0 6:-1,1,1 11:1,0,0 12:0,0,0 19:1,0,0 21:1,0,1
    1:-1,-1,0 6:1,0,0 9:-1,-1,0 15:-1,-1,1 19:1,-1,0 22:1,0,0
      | T(1:-1,-1,0) -> 6:1,0,0 9:-1,-1,0 11:1,-1,0 12:0,0,0 15:-1,-1,1 19:1,-1,0
    1:-1,0,0 3:1,0,0 15:-1,0,1 19:1,0,0 22:1,1,0
      | T(1:-1,0,0) -> 3:1,0,0 11:1,0,0 12:0,0,0 15:-1,0,1 19:1,0,0

The chains with an s3 move end in at least two fewer elements; those with T
moves end with as many elements and a lower top (in the multiset of orders,
the largest order removed exceeds the largest order added; orders compare
formally as (p | order, d), which is the comparison modulo p for p > 72).

## Q6. Reduction of the formal list (proved)

Let p ≥ 29, p ∉ P_cand, and S a minimal configuration modulo p, normalized as
in Q3 (it is connected). Take a spanning tree of its touch graph rooted at
x_0. Along an edge x - y the elements meet a common point, so
u_y = ε u_x o_y/o_x with ε = ±1 and offsets o_x, o_y; put ũ_{x_0} = 1 and
ũ_y = ε ũ_x o_y/o_x in G. The lift S̃ (same s, u replaced by ũ) reduces to S.
Two formal points ±ũ_x/o, ±ũ_y/o' of one layer that differ in G but agree
modulo p have ratio ±2^a 3^b with (a, b) ≠ (0, 0) and 2^a 3^b ≡ ±1 mod p; the
tree path from x to y has at most 5 edges, each moving the exponents by at
most (v, w), and the two offsets add at most (v, w), so |a| ≤ 6v ≤ 18,
|b| ≤ 6w ≤ 12 and p ∈ P_cand. So reduction is injective on the points of S̃,
the residual of S̃ at each formal point is that of S at its image, and S̃
satisfies (Q1.2) in G. A filter that fails for S̃ in G fails for S (the
(p+1)/2-filter is empty for 6 elements and p ≥ 29). So S̃ is a formal
configuration, and it is minimal (a formal sub-configuration reduces to one of
S, by Q3). Hence:

(a) S is, up to units, the reduction of one of the 16 configurations of Q5.

(b) Every minimal configuration modulo p has at least 5 elements, so a
    configuration B with at most 6 elements is minimal: if B' ⊊ B were a
    configuration, B - B' would satisfy (Q1.2) and the filters, so it would be
    a configuration with at most one element. The configurations modulo p are
    therefore, up to units, the reductions of the 16; all of them pass the
    filters, since the elements of each differ in the box |a| ≤ 18, |b| ≤ 12.

(c) The chains of Q5 reduce to chains. The steps of `lchain.py` (the move sets,
    hits, the negatives of the misses, cancellation of pairs, the zero tests,
    the sizes, and the order comparison of the end test) give the same result
    modulo p as formally when reduction is injective on the elements and
    their negatives occurring in the chain and dp > d' for all d, d' | 72.
    The second holds for p > 72. Two such elements (s, ε2^a 3^b),
    (s', ε'2^{a'}3^{b'}) with s' = ±s and different exponents collide only if
    p | 2^{a+}3^{b+} ∓ 2^{a-}3^{b-} for their difference of exponents;
    `chainprimes.py` lists these differences for all 16 chains (the
    configurations, the move sets and the intermediate multisets): |a| ≤ 2,
    |b| ≤ 1, and no prime ≥ 29 divides the resulting numbers (`CP.txt`). So
    reduction is injective on them for every p ≥ 29, and each formal chain is
    a chain modulo every p > 72.

So (i) holds for every prime p > 72 outside P_cand. Since every prime from 29
to 523 lies in P_cand, this is every prime outside P_exc.

Moves σ_{p,x} play no role in these chains. (For p ≥ 29 such a move fixes the
multiset when the coset x + (N/p)Z is closed under negation, and otherwise
gives at least p + 1 - |b| > 12 elements, so `lchain.py` with σ_p finds no
other chains than `fchain.py` without it.)

## Q7. The exceptional primes (checked)

(a) **p ∈ P_cand** (594 primes): `direct.py Pcand.txt modp` runs, at D = 72,
`prop 3 2 p`, `specialize.py` against the formal list and `levelchain.py`
with the backend `fchain.py` (`direct.log`, one line per prime). At every
prime the 16 reductions pass the filters, `prop` finds exactly them, except at
p = 31 one more configuration, and every configuration has a chain. All have
5 or 6 elements, so as in Q6(b) every configuration with at most 6 elements is
minimal and the `prop` list is complete (Q2, Q4).

The extra configuration at p = 31 has D_B = 2: at level 186 (L_B = 6) it is
{3, 99, 105, 117, 141}, all of order 62, the elements (s, u) = (3, 3·2^i),
i = 0, ..., 4, using 2^5 ≡ 1 mod 31. It has a chain (`modp/C_3_2_31.txt`):
in the unit multiple {21, 57, 75, 135, 177} (`levelchain.py` output,
`ex31/`), T(135) gives {21, 57, 75, 84, 93, 144, 177} and T(114) then gives
{57, 72, 75, 84, 177}: as many elements, two of order 62 replaced by two of
order 31.

(b) **p = 23.** Q2 does not apply, so `locDm 23 3 2 8` (= `m6/locD.c` at
N = 1656) gives the configurations directly: 17 up to units (`L_3_2_23.txt`),
the 16 reductions of Q5 and one more with D_B = 6, at level 138
{1, 22, 57, 63, 135, 136} (orders 138, 69, 46, 46, 46, 69). `levelchain.py 72
23 2 lchain` finds a chain for all 17 (`LC_3_2_23.txt`); for the extra one:
T(1) gives {22, 57, 63, 68, 69, 135}, so 1 (order 138) and 136 (order 69)
are replaced by 68 (order 69) and 69 (order 2) (`ex23/`).

(c) **p = 5, 7, 11, 13, 17, 19.** The parent's locD lists at D = 72
(`m6/L_3_2_p.txt`: 367, 133, 58, 44, 20, 19 configurations; at p ≤ 19 the
constants κ_ψ need not vanish and Q3 to Q6 do not apply) are run through
`levelchain.py 72 p 2 lchain` (`LC_3_2_p.txt`), which rescales each
configuration to level L_B p and calls `lchain.py` at depth 2. The
configurations without a chain:

| p | without chain | by D_B: count × size |
|---|---|---|
| 5 | 82 | 3: 1×3; 4: 1×3; 6: 2×2, 1×3, 3×4, 4×6; 8: 1×5; 12: 1×2, 1×3, 11×4, 12×5, 30×6; 18: 3×6; 24: 1×4, 1×5, 9×6 |
| 7 | 27 | 3: 1×4; 4: 1×3, 1×6; 6: 3×3, 1×4, 1×5, 3×6; 8: 1×6; 12: 3×5, 11×6; 24: 1×6 |
| 11 | 11 | 4: 1×6; 6: 1×3, 1×4, 1×5, 7×6 |
| 13 | 9 | 6: 1×3, 1×4, 7×6 |
| 17 | 3 | 6: 3×6 |
| 19 | 3 | 6: 3×6 |

A chain at level L_B p is a chain at level 72p (multiplication by 72/L_B
carries the moves to moves), and these counts equal those of the parent at
level 72p, so the two lists coincide. The D_B and sizes
agree with the table of `sec14-global.md` restricted to D_B | 72. The lists
are in Q8. For D | 72 the configurations at level Dp are those with D_B | D.

(d) **Non-exceptional primes.** 541 and 739 are the two least primes ≥ 29
outside P_cand, where (i) rests on Q6. There `prop V W p` gives exactly the
reductions of the formal list (`specialize.py`: 8, 12, 16 configurations at
D = 6, 12, 24 for p = 541, and 8, 12 at D = 6, 12 for p = 739), and
`locDm p V W K 5` (locD with at most 5 elements) finds exactly the
configurations of `prop V W p 5`: 2, 3, 4 at D = 6, 12, 24 for p = 541 and
2, 3 at D = 6, 12 for p = 739, the reductions of the formal configurations
with 5 elements (`Y/`). A locD run with 6 elements at a prime outside P_exc
was not made (at D = 6, p = 541 its table has 5.7·10^9 triples); locD with 6
elements is compared with prop at p = 29 to 43 (Q4) and with the formal list
at p = 23 ((b)).

## Q8. The configurations without a chain for p ≤ 19

Each configuration is given at level L_B p by its elements x/ord x (up to
units of Z/(L_B p); repeated elements are repeated).

p = 5:

```
D_B=3  level 15  size 3 : 1/15 6/5 13/15
D_B=4  level 20  size 3 : 1/20 12/5 17/20
D_B=6  level 30  size 2 : 1/30 19/30
D_B=6  level 30  size 2 : 1/30 24/5
D_B=6  level 30  size 3 : 1/30 7/30 27/10
D_B=6  level 30  size 4 : 1/30 1/30 19/30 19/30
D_B=6  level 30  size 4 : 1/30 1/30 19/30 24/5
D_B=6  level 30  size 4 : 1/30 1/30 24/5 24/5
D_B=6  level 30  size 6 : 1/30 1/30 1/30 19/30 19/30 19/30
D_B=6  level 30  size 6 : 1/30 1/30 1/30 19/30 19/30 24/5
D_B=6  level 30  size 6 : 1/30 1/30 1/30 19/30 24/5 24/5
D_B=6  level 30  size 6 : 1/30 1/30 1/30 24/5 24/5 24/5
D_B=8  level 40  size 5 : 1/40 3/40 11/40 32/5 33/40
D_B=12 level 60  size 2 : 1/60 49/60
D_B=12 level 60  size 3 : 2/30 21/20 57/20
D_B=12 level 60  size 4 : 1/60 1/60 49/60 49/60
D_B=12 level 60  size 4 : 1/60 2/30 38/30 49/60
D_B=12 level 60  size 4 : 1/60 2/30 48/5 49/60
D_B=12 level 60  size 4 : 1/60 7/60 43/60 49/60
D_B=12 level 60  size 4 : 1/60 14/30 26/30 49/60
D_B=12 level 60  size 4 : 1/60 14/30 36/5 49/60
D_B=12 level 60  size 4 : 1/60 17/60 49/60 53/60
D_B=12 level 60  size 4 : 1/60 23/60 47/60 49/60
D_B=12 level 60  size 4 : 1/60 24/5 46/30 49/60
D_B=12 level 60  size 4 : 1/60 34/30 46/30 49/60
D_B=12 level 60  size 4 : 3/20 4/15 51/20 52/15
D_B=12 level 60  size 5 : 1/60 2/30 14/30 49/60 54/10
D_B=12 level 60  size 5 : 1/60 2/30 26/30 42/10 49/60
D_B=12 level 60  size 5 : 1/60 4/15 24/5 49/60 52/15
D_B=12 level 60  size 5 : 1/60 4/15 28/15 48/5 49/60
D_B=12 level 60  size 5 : 1/60 8/15 36/5 49/60 56/15
D_B=12 level 60  size 5 : 2/30 2/30 21/20 38/30 57/20
D_B=12 level 60  size 5 : 2/30 2/30 21/20 48/5 57/20
D_B=12 level 60  size 5 : 2/30 3/20 26/30 48/5 51/20
D_B=12 level 60  size 5 : 2/30 3/20 36/5 38/30 51/20
D_B=12 level 60  size 5 : 2/30 3/20 38/30 39/20 48/5
D_B=12 level 60  size 5 : 2/30 3/20 39/20 48/5 48/5
D_B=12 level 60  size 5 : 2/30 9/20 14/30 48/5 57/20
D_B=12 level 60  size 6 : 1/60 1/60 1/60 49/60 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 2/30 38/30 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 2/30 48/5 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 7/60 43/60 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 14/30 26/30 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 14/30 36/5 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 17/60 49/60 49/60 53/60
D_B=12 level 60  size 6 : 1/60 1/60 23/60 47/60 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 24/5 46/30 49/60 49/60
D_B=12 level 60  size 6 : 1/60 1/60 34/30 46/30 49/60 49/60
D_B=12 level 60  size 6 : 1/60 2/30 2/30 38/30 38/30 49/60
D_B=12 level 60  size 6 : 1/60 2/30 2/30 38/30 48/5 49/60
D_B=12 level 60  size 6 : 1/60 2/30 2/30 48/5 48/5 49/60
D_B=12 level 60  size 6 : 1/60 2/30 7/60 38/30 43/60 49/60
D_B=12 level 60  size 6 : 1/60 2/30 7/60 43/60 48/5 49/60
D_B=12 level 60  size 6 : 1/60 2/30 17/60 38/30 49/60 53/60
D_B=12 level 60  size 6 : 1/60 2/30 17/60 48/5 49/60 53/60
D_B=12 level 60  size 6 : 1/60 2/30 23/60 38/30 47/60 49/60
D_B=12 level 60  size 6 : 1/60 2/30 23/60 47/60 48/5 49/60
D_B=12 level 60  size 6 : 1/60 14/30 14/30 26/30 26/30 49/60
D_B=12 level 60  size 6 : 1/60 14/30 14/30 26/30 36/5 49/60
D_B=12 level 60  size 6 : 1/60 14/30 14/30 36/5 36/5 49/60
D_B=12 level 60  size 6 : 1/60 24/5 24/5 46/30 46/30 49/60
D_B=12 level 60  size 6 : 1/60 24/5 34/30 46/30 46/30 49/60
D_B=12 level 60  size 6 : 1/60 34/30 34/30 46/30 46/30 49/60
D_B=12 level 60  size 6 : 2/30 3/20 4/15 48/5 51/20 52/15
D_B=12 level 60  size 6 : 2/30 4/15 21/20 24/5 52/15 57/20
D_B=12 level 60  size 6 : 2/30 4/15 21/20 28/15 48/5 57/20
D_B=12 level 60  size 6 : 2/30 9/20 16/15 28/15 48/5 57/20
D_B=12 level 60  size 6 : 2/30 16/15 21/20 28/15 36/5 57/20
D_B=18 level 90  size 6 : 1/90 4/45 22/45 57/30 62/45 74/45
D_B=18 level 90  size 6 : 1/90 4/45 22/45 62/45 72/5 74/45
D_B=18 level 90  size 6 : 1/90 4/45 37/90 38/45 62/45 78/15
D_B=24 level 120 size 4 : 1/120 49/120 83/120 107/120
D_B=24 level 120 size 5 : 3/40 9/40 33/40 76/30 99/40
D_B=24 level 120 size 6 : 1/120 2/60 49/120 83/120 98/60 107/120
D_B=24 level 120 size 6 : 1/120 4/30 49/120 76/30 83/120 107/120
D_B=24 level 120 size 6 : 1/120 4/30 49/120 83/120 96/5 107/120
D_B=24 level 120 size 6 : 1/120 14/60 49/120 83/120 86/60 107/120
D_B=24 level 120 size 6 : 1/120 24/5 49/120 83/120 107/120 116/30
D_B=24 level 120 size 6 : 1/120 28/30 49/120 52/30 83/120 107/120
D_B=24 level 120 size 6 : 3/40 4/30 33/40 51/40 81/40 108/10
D_B=24 level 120 size 6 : 3/40 8/15 33/40 51/40 81/40 104/15
D_B=24 level 120 size 6 : 3/40 9/40 28/30 33/40 99/40 108/10
```

p = 7:

```
D_B=3  level 21  size 4 : 1/21 4/21 18/7 19/21
D_B=4  level 28  size 3 : 1/28 9/28 25/28
D_B=4  level 28  size 6 : 1/28 1/28 9/28 9/28 25/28 25/28
D_B=6  level 42  size 3 : 1/42 24/7 38/21
D_B=6  level 42  size 3 : 1/42 25/42 37/42
D_B=6  level 42  size 3 : 1/42 30/7 32/21
D_B=6  level 42  size 4 : 1/42 15/14 31/42 37/42
D_B=6  level 42  size 5 : 1/42 2/21 25/42 38/21 39/14
D_B=6  level 42  size 6 : 1/42 1/42 24/7 24/7 38/21 38/21
D_B=6  level 42  size 6 : 1/42 1/42 30/7 30/7 32/21 32/21
D_B=6  level 42  size 6 : 1/42 2/21 30/7 30/7 31/42 32/21
D_B=8  level 56  size 6 : 1/56 9/56 11/56 25/56 43/56 51/56
D_B=12 level 84  size 5 : 1/84 13/84 24/7 75/28 76/21
D_B=12 level 84  size 5 : 1/84 13/84 36/7 64/21 75/28
D_B=12 level 84  size 5 : 1/84 13/84 38/42 62/42 75/28
D_B=12 level 84  size 6 : 2/42 3/28 15/28 62/42 74/42 75/28
D_B=12 level 84  size 6 : 2/42 3/28 15/28 64/21 72/7 75/28
D_B=12 level 84  size 6 : 2/42 3/28 27/28 48/7 75/28 76/21
D_B=12 level 84  size 6 : 2/42 3/28 27/28 50/42 74/42 75/28
D_B=12 level 84  size 6 : 2/42 3/28 27/28 60/7 64/21 75/28
D_B=12 level 84  size 6 : 2/42 9/28 48/7 57/28 76/21 81/28
D_B=12 level 84  size 6 : 2/42 9/28 50/42 57/28 74/42 81/28
D_B=12 level 84  size 6 : 2/42 9/28 57/28 60/7 64/21 81/28
D_B=12 level 84  size 6 : 2/42 12/7 27/28 39/28 75/28 76/21
D_B=12 level 84  size 6 : 2/42 15/28 24/7 39/28 75/28 76/21
D_B=12 level 84  size 6 : 2/42 15/28 36/7 39/28 64/21 75/28
D_B=24 level 168 size 6 : 1/168 25/168 79/168 121/168 127/168 151/168
```

p = 11:

```
D_B=4  level 44  size 6 : 1/44 5/44 13/44 24/11 37/44 41/44
D_B=6  level 66  size 3 : 1/66 25/66 62/33
D_B=6  level 66  size 4 : 1/66 8/33 50/33 62/33
D_B=6  level 66  size 5 : 1/66 25/66 31/66 37/66 49/66
D_B=6  level 66  size 6 : 1/66 1/66 25/66 25/66 62/33 62/33
D_B=6  level 66  size 6 : 1/66 1/66 25/66 37/66 50/33 62/33
D_B=6  level 66  size 6 : 1/66 2/33 25/66 37/66 49/66 62/33
D_B=6  level 66  size 6 : 1/66 5/66 25/66 46/33 59/66 62/33
D_B=6  level 66  size 6 : 1/66 7/66 20/33 25/66 61/66 62/33
D_B=6  level 66  size 6 : 1/66 7/66 20/33 37/66 50/33 61/66
D_B=6  level 66  size 6 : 1/66 7/66 37/66 38/33 43/66 50/33
```

p = 13:

```
D_B=6  level 78  size 3 : 1/78 55/78 61/78
D_B=6  level 78  size 4 : 1/78 32/39 61/78 62/39
D_B=6  level 78  size 6 : 1/78 1/78 55/78 55/78 61/78 61/78
D_B=6  level 78  size 6 : 1/78 7/78 37/78 55/78 61/78 73/78
D_B=6  level 78  size 6 : 1/78 9/26 20/39 56/39 73/78 75/26
D_B=6  level 78  size 6 : 1/78 12/13 43/78 55/78 60/13 63/26
D_B=6  level 78  size 6 : 1/78 20/39 21/26 45/26 73/78 74/39
D_B=6  level 78  size 6 : 1/78 20/39 43/78 45/26 62/39 63/26
D_B=6  level 78  size 6 : 1/78 25/78 43/78 49/78 55/78 61/78
```

p = 17:

```
D_B=6  level 102 size 6 : 1/102 7/102 13/102 81/34 91/102 96/17
D_B=6  level 102 size 6 : 1/102 7/102 39/34 55/102 91/102 96/17
D_B=6  level 102 size 6 : 1/102 7/102 55/102 57/34 78/17 91/102
```

p = 19:

```
D_B=6  level 114 size 6 : 1/114 7/114 78/19 79/114 86/57 91/114
D_B=6  level 114 size 6 : 1/114 13/114 43/114 72/19 103/114 110/57
D_B=6  level 114 size 6 : 1/114 13/114 43/114 80/57 102/19 103/114
```

## Files (`scratch-checks/forkB/`)

Scripts: prop.c (propagation search, formal or modulo p ≥ 29), locDm.c
(multipass `m6/locD.c`), cmp.py, fchain.py, randtest.py, levelchain.py,
specialize.py, chainprimes.py, cand.py, direct.py, run23.sh, runsmall.sh,
rundirect.sh, runx.sh, runy.sh. Data: F_V_W.txt (formal lists), FC_3_2.txt
and fdump/ (formal chains), CP.txt, Pcand.txt, direct.log, L_3_2_23.txt,
LC_3_2_p.txt (p = 5 to 23), P_V_W_p.txt, L_*_29.txt and X_*_29.txt (Q4), Y/
(Q7(d)), ex23/ and ex31/ (the two extra chains), modp/ (p = 31 only; the 1188
output files at all 594 primes of P_cand are summarised by
direct.log). README.txt lists them.
