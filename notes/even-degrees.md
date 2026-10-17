# Even degrees: the local argument at a top order 2e*

Working notes for the Fermat fourfold paper. Language and labels are those of
e84hc (`paper/sections/s3b_fermatfour.tex`, `s3c_fermatodd.tex`,
`s3d_fermat114.tex`): balanced multisets of nonzero elements of Z/M, pairs,
algebraic multisets, the standard multisets sigma_{p,i} and
T(i) = sigma_{2,i} = {i, i+M/2, -2i, M/2} (algebraic at every M,
lem:standardalg), moves (def:move, lem:move), the profile, lem:movecrit,
lem:fiberline, the character relation eq:charrel, split functions (S1)-(S4),
lem:grid, lem:oddbig, lem:twoD, prop:core.

Each statement below is marked **proved** (a hand proof written here),
**checked** (a finite computation, script named) or **open**.

## 0. Setting

M is even and prime to 3 (multiples of 6 are treated separately, Section 9).
A is a sextuple at level M: a balanced multiset of six nonzero elements that
contains no pair, generates Z/M and is not the union of two zero-sum triples.
The aim is to show that A has a direct or lowering move, possibly after a
chain of standard moves, outside an explicit finite list. By induction on
(M, profile) this gives the algebraicity of every balanced sextuple at level M.

A *move* with an algebraic balanced multiset sigma and S = sigma ∩ A replaces
A by A'' = (A - S) + (-(sigma \ S)); then A'' + sigma = A + pairs, so A is
algebraic if A'' is (proof of lem:move). After removing pairs, the move is
*direct* if at most four elements remain, *lowering* if six remain with smaller
profile, and it also succeeds if six remain that do not generate Z/M (lower
level) or form a split sextuple.

## 1. Every maximal order is even (proved)

Let e be an odd maximal order of A (maximal for divisibility among the orders
of the elements of A). Then e is prime to 6 here. With c = e in eq:charrel only
the elements of order e enter, so the odd function F of the elements of order
e is split along (K_p)_{p|e} on every coset of H, with mass 2N_e <= 12, and
prop:core applies.

* Case (1): F >= 1 on a line wK_p with p in {5,7}. If e = p then K_p = U
  contains -1, against oddness; so e != p, |K_p| >= (p+1)/2, and
  lem:fiberline gives a direct or lowering move.
* Case (2): e = 35 and the mass of F is 12 = 2N_e, so all six elements have
  order 35. They lie in the subgroup of order 35 and cannot generate Z/M, as
  M is even.

So every maximal order is even. In particular, if e* is a maximal element of
the set of odd parts of the orders in A, some element has order 2^j e* with
j >= 1. Sections 2-7 treat j = 1 (written 2 || e); Section 8 treats 4 | e.

## 2. Notation at a top order e = 2e*, e* odd (2 || e), e* prime to 3

Let e* be maximal among the odd parts of the orders in A, with 2e* an order in
A and 4e* not. U* = (Z/e*)^x. For v in U*:

* "F at v" is the element (M/e)u with u odd, u ≡ v mod e*; it has order e.
* "E at v" is the element (M/e)u with u even, u ≡ v mod e*, that is
  (M/e*)(v/2); it has order e*.

F(v) and E(v) are the multiplicity at v minus the multiplicity at -v. As A has
no pair, |F(v)| = mult(F at v) + mult(F at -v), and likewise for E; the masses
are 2N_e and 2N_{e*}. A *top* is an element F at v of A (so F(v) >= 1).

For x = F at v: x + M/2 = E at v, -2x = E at -2v, so
T(x) = {F at v, E at v, E at -2v, M/2}.

**Character relation (proved).** For an odd primitive character chi of
conductor e*, the elements a with e* | f_a are those of order e* and e (by the
choice of e*), and eq:charrel reads
chi(2) Ê(chi) + (1 - chi(2)) F̂(chi) = 0, since z_a = v/2 for E at v and
phi(e) = phi(e*). Hence Ê = (1 - chi̅(2)) F̂, where
f̂(chi) = sum_v f(v) chi̅(v).

**The function E_1 (proved).** Put E_1(w) = E(w) - F(w) + F(w/2). Then
Ê_1(chi) = 0 for every odd primitive chi mod e*, and E_1 is odd, so by the
proof of lem:splitF, E_1 is split along (K_p)_{p|e*} on every coset of H*.
E_1 is the odd counting function of the elements of order e* of the multiset

  A_1 = A - (tops) + sum over tops x of {E at -v, E at 2v, M/2},

obtained by subtracting T(x) from A for every top and removing the pairs
{x, -x}: indeed A + (-T(x)) contains x and -x.

## 3. The elementary moves (proved)

Let x = F at v be a top. Each of the following lowers the profile: it removes
elements of order e or e* and adds elements of order e*, or 2, and removes at
least one element of order e, while the elements of larger order stay.

* (b) T-pair: x and x + M/2 = E at v both in A. S = {x, x + M/2}:
  A'' = A - x - (x + M/2) + 2x + M/2.
* (c) x and -2x = E at -2v both in A. S = {x, -2x}:
  A'' = A - x - (-2x) + (E at -v) + M/2.
* (d) tops x_i = F at 2v_j and x_j = F at v_j. Then -2x_j = -x_i + M/2, and
  [A''] - [A] = -[T(x_i)] - [T(x_j)] modulo pairs for
  A'' = A - x_i - x_j + 2x_i + (-x_j - M/2).
* (e) M/2 in A. S = {x, M/2}: A'' = A - x - M/2 + (E at -v) + (E at 2v).

From now on A has none of the moves (b)-(e) and no fibre move
(lem:movecrit) for its elements of order e or e*.

**Sign identity (proved).** |E_1(w)| = |E(w)| + |F(w)| + |F(w/2)| for all w.
The three terms E(w), -F(w), F(w/2) never have opposite signs:
(E(w), -F(w)) opposite means a T-pair (b); (-F(w), F(w/2)) opposite means tops
at w and w/2, or at -w and -w/2 (d); (E(w), F(w/2)) opposite means E at w with
F at -w/2, or E at -w with F at w/2 (c). Consequences:

* mass(E_1) = 2N_{e*} + 4N_e <= 24, since N_e + N_{e*} <= 6;
* E_1(v) <= -1 and E_1(2v) >= 1 at every top v, hence E_1 >= 1 at -v and
  <= -1 at -2v; in particular E_1 != 0;
* the elements of order e* of A_1 carry no pair, and their multiset is the
  positive part of E_1.

## 4. Prime and prime-power e* (proved)

* e* = p prime: K_p = U*, so E_1 is constant, and odd, so E_1 = 0, against
  Section 3.
* e* = p^k, k >= 2, p >= 5: H* = K_p = 1 + p^{k-1}Z has order p and E_1 is
  K_p-invariant. The cosets vK, -vK, 2vK, -2vK are distinct (-1, 2, -2 are
  not congruent to 1 mod p^{k-1}, as p >= 5), and E_1 is nonzero on each, so
  the mass is at least 4p <= 24, p = 5, and |E_1| = 1 exactly on these four
  cosets (a fifth coset or a value 2 adds 5). The negative cosets are vK and
  -2vK, the positive ones 2vK and -vK. A top w in -2vK would have 2w in -4vK,
  which is neither 2vK (needs -2 in K) nor -vK (needs 4 in K). So all tops lie
  in vK, are distinct (|F| <= |E_1| = 1), and 20 = 2N_{e*} + 4N_e with
  N_e + N_{e*} <= 6 forces N_e >= 4 >= 3 distinct elements of order e in one
  fibre Phi_5(x); lem:movecrit gives a move. Contradiction.

So e* has at least two distinct prime factors.

## 5. The compound move (proved)

**Lemma (line sums).** Suppose E_1 = sum_i s_i 1_{L_i} with s_i = ±1 and
lines L_i = w_i K_{p_i} (any primes p_i | e*), such that
|E_1| = sum_i 1_{L_i}. Then A has a direct or lowering chain of moves.

Proof. Pass from A to A_1 (Section 2). The order-e* part of A_1 is the multiset
sum of the lines with s_i = +1, as sets of elements: a line along K_p with
p || e* is the set of the p - 1 elements of order e* in a fibre Phi_p(y), and
with p^2 | e* it is the whole fibre. A move sigma_{p,y} removes such a line and
adds -y_0, p y (y_0 the element of order e*/p in the fibre) when p || e*, or
p y when p^2 | e*: at most two elements per line. Each line has at least four
points, and the positive lines carry mass(E_1)/2 = N_{e*} + 2N_e points, so
there are at most (N_{e*} + 2N_e)/4 of them. With L_0 = 6 - N_e - N_{e*} low
elements and eps = N_e mod 2 (the copies of M/2 pair off), the final multiset
has at most L_0 + eps + (N_{e*} + 2N_e)/2 = 6 + eps - N_{e*}/2 elements; its
size is even, so at most 6. It has no element of order e and no element of
order larger than e that A did not have, so the chain is direct or lowering.

## 6. Two primes (proved, except e* in {35, 55})

Let e* = p^a q^b. If a, b <= 1, then H* = U* = (Z/p)^x × (Z/q)^x and
E_1(y, x) = alpha(x) + beta(y) with alpha, beta odd (adjust by a constant),
both in Z or both in 1/2 + Z. Pairing (y, x) with (-y, x):
mass = sum_{y,x} max(|alpha(x)|, |beta(y)|).

* Half-integral: mass >= phi(e*)/2, so phi(e*) <= 48: e* in {35, 55, 65}.
  For e* = 65 equality holds, |alpha| = |beta| = 1/2, mass 24, so N_e = 6,
  N_{e*} = 0, and E_1 = -1 on N = N_u × N_v (N_u ⊂ (Z/5)^x, N_v ⊂ (Z/13)^x the
  sets where the signs are -1, of sizes 2 and 6). The tops T satisfy
  N = T ⊔ (-2T) and 2T ⊂ -N, so T ⊂ (N_u ∩ 2N_u) × (N_v ∩ (-1/2)N_v) (using
  -1/2 = 2 mod 5). In (Z/5)^x = <2>, |N_u ∩ 2N_u| = 1 for each of the four
  odd sign patterns, so |T| = 6 forces N_v = -2N_v; but -2 generates
  (Z/13)^x, so N_v would be everything. Contradiction.
* Integral, alpha and beta both nonzero: mass >= 2(p - 1) + 2(q - 1) - 4, so
  p + q <= 16: e* in {35, 55}.
* Integral, one of them zero: E_1 is invariant under one K_p, a line sum as in
  Section 5.

If a >= 2 or b >= 2: **open** (hand proof to write; no configuration exists for
e* <= 301 other than 5 || e*, checked).

## 7. What the computations show (checked)

* `scratch-checks/loc3.c`: every local configuration at a top order 2e*,
  e* <= 301 prime to 3 (no pair, no T-pair, no fibre move, E_1 exactly split).
  Configurations occur only at e* in {7, 25, 31} (all with a move (c) or (d)),
  35 (31), 55 (6) and 5q for q = 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49,
  53, 59 (2 or 4 each).
* `scratch-checks/compound.py`: after removing those with moves (c), (d), the
  compound move succeeds for all of them except four at e* = 35 and two at
  e* = 55. The shape at 5q is E_1 = -1_L + 1_{2L} + 1_{-L} - 1_{-2L} along K_5
  with N_e = 2, N_{e*} = 4: all six elements lie in the subgroup of order 10q,
  so this occurs only at M = 10q (proved by hand: |E_1| = 1 on L forces
  distinct tops, so N_e <= 2 by lem:movecrit, and mass 16 forces N_{e*} = 4).
* The stuck configurations: at 35, {F1, F26, E24, E27} with two low elements,
  {F1, F3, F8, F24, E6, E27}, {F1, E4, E9, E27, E32} and {F1, E9, E17, E24, E27}
  with one low element; at 55, {F1, F16, F26, F31, F36} with one low element and
  {F1, F16, F26, F31, E17, E19}. Except the first, every one has all six
  elements in the subgroup of order 70 or 110, so it occurs only at M = 70 or
  M = 110.
* `scratch-checks/fullmove.c` with `fsweep.sh` (depth-4 chains of standard
  moves sigma_{l,x}, T(x), all even M <= 400): the sextuples with no
  successful chain occur only at M in {60, 66, 70, 78, 84, 110, 114, 132,
  156, 168, 210, 330}. Degrees 14, 20, 28, 50, 62, 140, 220, 280 have none.

## 8. Top orders divisible by 4: open

The sweep shows that 20 and 28 reduce through chains of moves. A hand version
of Sections 2-6 with three types (orders e, e/2, e/4) is to be written.

## 9. Multiples of 6 and the exceptional degrees: open

The residual degrees 60, 66, 78, 84, 114, 132, 156, 168, 210 have the Hodge
conjecture by known theorems (Aoki for 2^a 3^b 5^c 7^d with c = 0 or d = 0;
Peterson for 70, 140, 210; e84hc Theorem A for 66, 78, 114, 132, 156), and
70 by Peterson. The residual at 330, [5, 40, 66, 250, 310, 319], needs its own
argument. 110 stays open.
