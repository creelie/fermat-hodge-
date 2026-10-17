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

Let e* be maximal among the odd parts of the orders in A, such that the
largest order of A with odd part e* is 2e*. U* = (Z/e*)^x. For v in U*:

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

## 6. Split functions of mass at most 8 (proved)

Notation of e84hc Step 4: K_1, ..., K_r with direct product H, C a coset of H,
H' = K_2 ... K_r, slices S_c = x c H' for c in K_1, mu(c) the mass of f on S_c;
(S1)-(S4) as there.

**Lemma S.** Let |K_i| >= 4 for all i, with equality for at most one i, and
suppose that subgroups of different index i have different orders. Let
f: C -> Z be split along (K_1, ..., K_r), not identically zero, with
sum_C |f| <= 8. Then f is one of

* (i) sigma 1_L, L a line along some K_i (so |K_i| <= 8);
* (ii) 2 sigma 1_L, L a line along the K_i of order 4;
* (iii) sigma 1_L + sigma' 1_L', L != L' lines along the K_i of order 4;
* (iv) a *cross* sigma (1_L - 1_L'), L a line along a K_i of order 6, L' a line
  along a K_j of order 4, |L ∩ L'| = 1 (mass 8).

In particular every nonzero split function has mass at least min |K_i|.

Proof. Induction on r; r = 0 is excluded, and for r = 1, f is constant on the
line C (S4), giving (i) or (ii). Let r >= 2 and K = K_1 of largest order; then
|K| >= 5 and |K| > m' := min_{i>=2} |K_i| >= 4.

* Case A, f is K-invariant: a nonzero value c on a line z_0 K gives
  |c| |K| <= 8, so |c| = 1, and a second line would add |K| >= 5: (i).
* Case B1, some mu(c_0) = 0: by (S2) f is split along (K_2, ..., K_r) on every
  slice. A nonzero slice carries mass >= m' >= 4 by induction, so at most two
  slices are nonzero. One slice: f is one of (i)-(iv) inside it. Two slices:
  each has mass 4, so is sigma 1_L with |L| = 4: (iii).
* Case B2, f is not K-invariant and mu >= 1 on every slice: as
  sum mu <= 8 < 2|K|, some c_s has mu(c_s) = 1. For c in K put
  g_c(z) = f(z) - f(z c^{-1} c_s) on S_c, split along (K_2, ..., K_r) by
  (S1). If every g_c vanished, f would be K-invariant; let D be the set of c
  with g_c != 0, d = |D| >= 1. For c in D, g_c has mass >= m' by induction, so
  mu(c) >= m' - 1. Hence 8 >= d(m' - 1) + (|K| - d), that is
  |K| + d(m' - 2) <= 8. With |K| >= m' + 1 this forces m' = 4, d = 1,
  |K| <= 6, and |K| = 5 is excluded (orders 4 and 5 would both belong to the
  prime 5). So |K| = 6, every inequality is an equality, mu(c_1) = 3 on the
  one c_1 in D and mu = 1 elsewhere. Off S_{c_1}, f is sigma at the points of
  one line L along K; on S_{c_1}, g_{c_1} has mass 4, so equals -sigma 1_{L'}
  for a line L' along the subgroup of order 4 through the point of L in
  S_{c_1} (mass 3 forces the cancellation): (iv).

For the subgroups K_p (p >= 5, e* prime to 3) the hypotheses hold by e84hc
lem:Kp(a): |K_p| is p - 1 or p, these sets are disjoint for different primes,
and the order 4 occurs only for 5 || e*; a cross needs 5 || e* and 7 || e*.
(Checked by brute force on the grids of orders (4,6), (5,6), (4,7):
`scratch-checks/lemS.py`.)

A sum of lines sum_i s_i 1_{L_i} with |f| = sum_i 1_{L_i} is called a
*non-cancelling line sum*; (i)-(iii) are such sums, (iv) is not.

## 7. Non-squarefree e* (proved)

Let p^2 | e* for some p, and R = prod_{p^2 | e*} p^{v_p(e*) - 1} >= 5.

* H* = {u in U* : u ≡ 1 mod R}: each K_p lies in it, and both have order
  prod_{p || e*} (p - 1) prod_{p^2 | e*} p.
* Hence -1, 2, -2, 4 are not in H* (R does not divide 2, 1, 3, 3), and -4 is in
  H* only for R = 5.

Let v be a top. The cosets X_1 = vH*, X_2 = -vH*, X_3 = 2vH*, X_4 = -2vH* are
distinct, and E_1 is nonzero on each (Section 3), so each carries mass >= 4 by
Lemma S. By oddness mu(X_1) = mu(X_2) = a and mu(X_3) = mu(X_4) = b, and
2a + 2b <= 24, so a, b <= 8, and every other coset has mass <= 4. By Lemma S,
E_1 is on every coset of type (i)-(iv).

If no coset carries a cross, E_1 is a non-cancelling line sum and Section 5
gives a move. A cross needs 5 || e* and 7 || e*, so R >= 11. A coset with a
cross has mass 8, hence is one of the X_i; then a + b = 12, the mass of E_1 is
24 = 2N_{e*} + 4N_e, so N_e = 6, N_{e*} = 0, E_1 vanishes off the X_i, and
{a, b} = {4, 8}. With E = 0, the negative part of E_1 is the multiset
T + (-2T), T the six tops. A top t in X_3 or X_4 would have 2t in ±4vH*, which
is none of the X_i (R != 5); so T lies in X_1 ∪ X_2 and -2T in X_3 ∪ X_4. The
negative mass on X_1 ∪ X_2 is then |T| = 6; by oddness it is mu(X_1) = a, which
is 4 or 8. Contradiction.

So for non-squarefree e* the compound move always succeeds (this also covers
prime powers, Section 4).

## 8. Squarefree e* with at least three primes (proved)

Here H* = U*. Let p_1 be the largest prime (p_1 >= 11), K = K_{p_1} of order
p_1 - 1 >= 10, H' the product of the other K_p, slices S_c for
c in (Z/p_1)^x. In coordinates U* = (Z/p_1)^x × (Z/(e*/p_1))^x write
-1 = eps eps' with eps = (-1, 1) in K and eps' = (1, -1) in H'. Then
mu(-c) = mu(c), and for z in S_c, E_1(z eps) = -E_1(z eps'), so by (S1)

  g(z) = E_1(z) + E_1(z eps')  is split along H' on S_c, with mass <= 2 mu(c).   (*)

Also eps' lies in no K_p of H': -1 ≡ 1 mod e*/(p p_1) fails since r >= 3.
A top v in S_c gives nonzero slices S_c, S_{-c}, S_{2c}, S_{-2c}, distinct as
p_1 >= 11.

* **Case Z, some slice vanishes.** By (S2) every slice is split along H',
  nonzero slices carry mass >= 4, so mu(c), mu(2c) <= 8 and the other slices
  carry <= 4. Lemma S applies on each slice; without a cross E_1 is a
  non-cancelling line sum (Section 5). A cross has mass 8, so lies on one of
  the slices ±c, ±2c of every top, the mass is 24, N_e = 6, N_{e*} = 0, and
  the support is in these four slices. A top in S_{±2c} would have 2t in
  S_{±4c}, outside them (4 ≢ ±1, ±2 mod p_1). So T lies in S_c ∪ S_{-c}, whose
  negative mass is then 6, while by oddness it is mu(c), which is 4 or 8.
* **Case NZ1, some mu(c) = 1.** In (*), g has mass <= 2 < 4, so g = 0; then
  E_1(z_0 eps') = -E_1(z_0) != 0 at a second point of S_c. (This is the
  argument of e84hc lem:oddbig.)
* **Case NZ2, all mu(c) >= 2.** Then 2(p_1 - 1) <= 24, so p_1 is 11 or 13. On a
  slice of mass 2, g in (*) has mass <= 4; if nonzero it is ±1_L with L a line
  along K_5 and g(z eps') = g(z), so L eps' = L and eps' in K_5, excluded. So
  E_1 = sigma(delta_{z_0} - delta_{z_0 eps'}) on every slice of mass 2. Two
  slices of mass 2 are translates of each other: their difference
  E_1(z) - E_1(z c^{-1} c') is split along H', of mass <= 4 and odd under
  eps', while a mass-4 split function is single-signed.
  - p_1 = 13: all twelve slices have mass 2, so E_1 is K-invariant,
    E_1 = sigma(1_L - 1_{L eps'}) for a line L along K_13: a line sum.
  - p_1 = 11, e* = 385, H' = K_5 × K_7 of orders 4, 6: at least six slices have
    mass 2, the others come in pairs ±c. For such c, the difference with a
    mass-2 slice is split, nonzero, of mass <= mu(c) + 2 <= 6, hence ±1_{L'}
    with L' a line along K_5 or K_7, which meets {z_0, z_0 eps'} in at most one
    point; so mu(c) >= 2 + 4 - 2 = 4. Then exactly the two slices ±c_1 differ,
    with mass 4 each, the total is 24, and N_e = 6. In coordinates (a, b) in
    (Z/11)^x × (Z/35)^x the support of E_1 is {b = ±b_0} ∪ {a = ±c_1,
    b in ±b_0 K_5}. For t in the support, 2t is outside it (2 ≢ ±1 mod 35,
    ±2 not in K_5, ±1/2 not in K_5, 2 ≢ ±1 mod 11). So there is no top:
    contradiction.

So for squarefree e* with r >= 3 primes the compound move always succeeds.

## 9. Two primes, squarefree (proved)

Let e* = pq. Then H* = U* = (Z/p)^x × (Z/q)^x and
E_1(y, x) = alpha(x) + beta(y) with alpha, beta odd (adjust by a constant),
both in Z or both in 1/2 + Z. Pairing (y, x) with (-y, x) (e84hc lem:twoD):
mass = sum_{y,x} max(|alpha(x)|, |beta(y)|).

* Half-integral: mass >= phi(e*)/2, so phi(e*) <= 48: e* in {35, 55, 65}.
  For e* = 65 equality holds, |alpha| = |beta| = 1/2, mass 24, so N_e = 6,
  N_{e*} = 0, and E_1 = -1 on N = N_u × N_v (N_u ⊂ (Z/5)^x, N_v ⊂ (Z/13)^x the
  sets where the signs are -1, of sizes 2 and 6). The tops T satisfy
  N = T ⊔ (-2T) and 2T ⊂ -N, so T ⊂ (N_u ∩ 2N_u) × (N_v ∩ (-1/2)N_v) (using
  -1/2 = 2 mod 5). In (Z/5)^x = <2>, |N_u ∩ 2N_u| = 1 for each of the four
  odd sign patterns, so |T| = 6 forces N_v = -2N_v; but -2 generates
  (Z/13)^x, so N_v would be everything. Contradiction.
* Integral, alpha and beta both nonzero: at least 2(p - 1) + 2(q - 1) - 4
  points have alpha(x) != 0 or beta(y) != 0, so p + q <= 16: e* in {35, 55}.
* Integral, one of them zero: E_1 is invariant under one K_p, a line sum.

**Min-size (proved).** In every case of Sections 4-9 the mass of E_1 is at least
16, except for half-integral functions at 35 (mass >= 12) and 55 (>= 20); for
the K_p-invariant case the four values at ±v, ±2v lie on four distinct lines.
So n = N_e + N_{e*} >= 4, unless e* = 35, mass 12 and (N_e, N_{e*}) = (3, 0).
That case is impossible: N = N_u × N_v (sizes 2 and 3) equals T ⊔ (-2T) with
|T| = 3, so T ⊂ (N_u ∩ 2N_u) × (N_v ∩ 3N_v) (-1/2 = 3 mod 7), and since
|N_u ∩ 2N_u| = 1 this forces N_v = 3N_v, impossible as 3 generates (Z/7)^x.

## 10. The exceptional tops 35 and 55 (proved)

**e* = 55.** A half-integral E_1 has mass >= 20 and an integral one with
alpha, beta != 0 has mass >= 24; so n >= 5, A has at most one low element,
which is minus the sum of the others and lies in the subgroup of order 110.
So such A occur only at M = 110.

**e* = 35, n >= 5.** As for 55, A lies in the subgroup of order 70: M = 70.

**e* = 35, n = 4.** The mass is 4N_e + 2N_{e*} <= 16.

* Integral with alpha, beta != 0: mass 16 forces alpha = ±(delta_{x_0} -
  delta_{-x_0}), beta = ±(delta_{y_0} - delta_{-y_0}) (two crosses) and
  (N_e, N_{e*}) = (4, 0). Listing the points t with E_1(t) <= -1 and
  E_1(2t) >= 1 gives exactly two, each with |E_1(t)| = 1, so at most two tops
  (|F| <= |E_1| by the sign identity), against N_e = 4.
* Half-integral: an entry |alpha| >= 3/2 or |beta| >= 3/2 adds at least 8, so
  the mass is 12 and (N_e, N_{e*}) = (2, 2), with two low elements y_1, y_2.
  This is *configuration 1*: the negative set N = N_u × N_v is
  (-W) ⊔ T ⊔ (-2T), W the positions of the two elements of order 35.
  Exactly as in the min-size argument, T ⊂ (N_u ∩ 2N_u) × (N_v ∩ 3N_v), so
  N_u = {c, -2c} and N_v = {g^k, g^{k+1}, g^{k+2}} (g = 3), with
  T = {(c, g^{k+1}), (c, g^{k+2})}, -W = {(c, g^k), (-2c, g^{k+2})}. The four
  elements lie in the subgroup of order 70; in Z/70 = Z/2 × Z/35 their sum is
  (0, t_1 + t_2 + w_1 + w_2), with 5-part 3c != 0 and 7-part 2g^k != 0. So
  s = y_1 + y_2 has order 35.

**Lemma C (carry).** Let 70 | M, B a multiset in the subgroup of order 70 and
A = B + {y_1, y_2} balanced (sum_{a in A} <ta> = 3 for every unit t, <a> the
fractional part of a/M), with y_1, y_2 != 0 and s = y_1 + y_2 of order 35. If
35 does not divide f = ord(y_1), then f | 70.

Proof. For a unit t, <ty_1> + <ty_2> = <ts> + delta(t) with
delta(t) = [<ty_1> > <ts>], and it equals 3 - sum_B <tb>, which depends only on
t mod 70; so delta(t) does too. Suppose f ∤ 70; let g_0 = gcd(f, 70) and
g_1 = gcd(f, 35), a divisor of 35 other than 35. As t runs over the units
≡ t' mod 70, <ty_1> runs over the set P of z/f with z a unit mod f,
z ≡ t' z_1 mod g_0 (CRT). P depends only on t' mod g_0, and by the above it
lies on one side of <t's> for every t' in that class mod g_0, i.e. for
t's = (M/35)w with w running over the units mod 35 with w ≡ w_0 mod g_1. These
w/35 cut [0, 1) into intervals of length at most 14/35 (g_1 = 7; at most 10/35
for g_1 = 5 and 3/35 for g_1 = 1). But P contains two points at distance at
least 1/2:

* if f has a prime l outside {2, 5, 7} (so l >= 11), with l^a || f, P contains
  the points z'/f + i/l^a for all i except one class mod l, which lie in no
  interval shorter than 1 - 2/l >= 9/11;
* otherwise 4, 25 or 49 divides f, every z ≡ c mod g_0 is a unit mod f, and P
  consists of h = f/g_0 >= 2 points spaced 1/h, spanning (h - 1)/h >= 1/2.

Contradiction. ∎

For configuration 1: if 35 | ord(y_i), then ord(y_i) is 35 or 70, since 35 is a
maximal odd part with largest order 70; otherwise Lemma C gives ord(y_i) | 70.
So A lies in the subgroup of order 70 and M = 70. (Checked: `scratch-checks/c35.c`
finds, for M = 70k with k <= 12, exactly one completion, of orders 7 and 5.)

## 11. Conclusion for 2 || e (proved)

**Theorem.** Let M be even and prime to 3 and A a sextuple at level M. If A
has a maximal odd part e* whose largest order is 2e*, then A has a direct or a
lowering move, or a chain of moves ending in at most six elements of lower
profile, unless M is 70 or 110.

Proof: moves (b)-(e) and fibre moves (Section 3); otherwise E_1 is a
non-cancelling line sum by Sections 4 and 7-9, and Section 5 applies, except
at e* in {35, 55}, which Section 10 confines to M in {70, 110}. Uniqueness of
the maximal odd part is not needed: any maximal odd part with largest order
2e* will do.

So the open case for M prime to 3 is: every maximal odd part e* of A has
largest order 2^J e* with J >= 2.

## 12. What the computations show (checked)

* `scratch-checks/loc3.c`: every local configuration at a top order 2e*,
  e* <= 301 prime to 3 (no pair, no T-pair, no fibre move, E_1 exactly split).
  Configurations occur only at e* in {7, 25, 31} (all with a move (c) or (d)),
  35 (31), 55 (6) and 5q for q = 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49,
  53, 59 (2 or 4 each), in agreement with Sections 4-10.
* `scratch-checks/compound.py`: after removing those with moves (c), (d), the
  compound move succeeds for all of them except four at e* = 35 and two at
  e* = 55, in agreement with Section 10. The shape at 5q is
  E_1 = -1_L + 1_{2L} + 1_{-L} - 1_{-2L} along K_5 with N_e = 2, N_{e*} = 4.
* `scratch-checks/fullmove.c` with `fsweep.sh` (depth-4 chains of standard
  moves sigma_{l,x}, T(x), all even M <= 400): the sextuples with no
  successful chain occur only at M in {60, 66, 70, 78, 84, 110, 114, 132,
  156, 168, 210, 330}. Degrees 14, 20, 28, 50, 62, 140, 220, 280 have none.
  For M prime to 3 the only ones are 70 and 110, so the case J >= 2 has no
  obstruction up to 400.
* `scratch-checks/g4.py` (moves with an arbitrary balanced 4-tuple through two
  elements of A) and `scratch-checks/dec.py` (splittings into two balanced
  4-tuples {a, b, c, -t}, {t, rest}): the residuals at 60, 66, 78, 84, 132,
  156, 330 and 390 have such a move or splitting. Every balanced 4-tuple is
  algebraic (Lefschetz), so these are valid moves.

## 13. Top orders divisible by 4: open

The case left for M prime to 3: every maximal odd part has largest order
2^J e* with J >= 2. For J = 2 write G_j at v (j = 0, 1, 2) for the elements
(M/(2^j e*))u of order 2^j e* with u ≡ v mod e*; for j = 2 there are two, with
u ≡ 1 or 3 mod 4, and minus one of them at v is the other at -v. With G_j the
odd counting functions on U*, eq:charrel at c = e* reads

  G_0^ + (1 - chi(2)) G_1^ + (1 - chi(2)) G_2^ / 2 = 0

for every odd primitive chi mod e*, and at c = 4e* the order-4e* elements give
a function on (Z/4e*)^x split along the subgroup of order 2 (whose lines are
the T-pairs {x, x + M/2}) and the K_p. A hand version of Sections 2-10 for
these three types is to be written.

## 14. Multiples of 6 and the exceptional degrees: open

The residual degrees 60, 66, 78, 84, 114, 132, 156, 168, 210 have the Hodge
conjecture by known theorems (Aoki for 2^a 3^b 5^c 7^d with c = 0 or d = 0;
Peterson for 70, 140, 210; e84hc Theorem A for 66, 78, 114, 132, 156), and
70 by Peterson; 330 is a multiple of 110. 110 stays open. A hand argument for
3 | M (where K_3 has order 2 or 3 and lem:grid fails) is to be written.
