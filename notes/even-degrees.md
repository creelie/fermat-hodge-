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

M is even and prime to 3 (multiples of 6 are treated separately, Section 14).
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
j >= 1. Sections 2-11 treat j = 1 (written 2 || e); Section 13 treats 4 | e.

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

The remaining case for M prime to 3, every maximal odd part e* of A having
largest order 2^J e* with J >= 2, is Section 13.

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
* `scratch-checks/loc4.c` (J = 2): every local configuration at a top order
  4e*, e* <= 25 prime to 3, with no pair, T-pair, move (c) or fibre line and
  with (R1), (R2) exact. Configurations occur only at e* = 5, 7, 11:
  {x_{+,1}, x_{+,2}, z_3} and its double at 5; {x_{+,1}, x_{+,2}, x_{+,4}}, its
  double, {x_{+,1}, x_{+,2}, x_{+,3}, z_4, z_5} and {x_{+,1}, x_{+,2}, x_{+,4},
  y_1, y_2, y_4} (which has move (d)) at 7; and (g) at 11, in agreement with
  13.4-13.6 (the doubles are shape II with c = 2).
* `scratch-checks/shape2.py`: the sets S of 13.5 with (p - 1)/2 + |F| <= 6,
  up to units, for p = 5, 7, 11, 13.
* `scratch-checks/cands4.py`, `scratch-checks/glob4.py`, `scratch-checks/chk44.py`:
  the finite check of 13.8 (all completions at M = 20, 28, 44, the chain at
  28, and a brute force over five elements of order 44 and one of order 11).

## 13. Top orders divisible by 4 (proved)

Here 4 | M and e* is a maximal odd part of A whose largest order is 2^J e*
with J >= 2. U* = (Z/e*)^x and H* is the product of the K_p, p | e*.

### 13.1 J = 2: notation and the two relations

For v in U*:

* x_{+,v}, x_{-,v}: the elements (M/4e*)u with u ≡ 1, resp. 3, mod 4 and
  u ≡ v mod e*; order 4e*.
* y_v = (M/2e*)u with u odd, u ≡ v mod e*; order 2e*.
* z_v = (M/e*)v; order e*.

Then -x_{+,v} = x_{-,-v}, x_{-,v} = x_{+,v} + M/2, 2x_{±,v} = y_v,
-2x_{±,v} = y_{-v}, y_v + M/2 = z_{v/2}, z_v + M/2 = y_{2v}, -2y_v = z_{-v}.
The elements of odd part e* are exactly these (maximality of e* and of J);
the others are called *low*. N_x, N_y, N_z count the elements of orders 4e*,
2e*, e*. Put

  P(v) = mult(x_{+,v}) - mult(x_{-,-v}),  Y(v) = mult(y_v) - mult(y_{-v}),
  Z(v) = mult(z_v) - mult(z_{-v}).

Y and Z are odd, P is neither; as A has no pair, sum |P| = N_x and the masses
of Y, Z are 2N_y, 2N_z. Write f^(chi) = sum_v f(v) chi̅(v); then
(f(2·))^ = chi(2) f^.

**(R1), conductor e* (proved).** For an odd primitive chi mod e*, the
elements a with e* | f_a are the x, y, z. In eq:charrel, z_v contributes
chi̅(v)/phi(e*), y_v contributes chi̅(v)(1 - chi(2))/phi(e*), x_{±,v}
contributes chi̅(v)(1 - chi(2))/(2 phi(e*)). Since chi is odd,
sum_v mult(z_v) chi̅(v) = Z^/2, likewise for Y, and
sum_v (mult(x_{+,v}) + mult(x_{-,v})) chi̅(v) = P^. Hence

  Z^ + (1 - chi(2)) (Y^ + P^) = 0.

**(R2), conductor 4e* (proved).** A primitive chi of conductor 4e* is
chi_4 psi with psi primitive mod e*, and chi is odd exactly when psi is even.
Only the elements of order 4e* enter, with chi̅(u) = ±psi̅(v) for x_{±,v}, so
sum_v (mult(x_{+,v}) - mult(x_{-,v})) psi̅(v) = 0, that is P^(psi) = 0 for
every even primitive psi mod e*.

**Consequences.**

* D = P + P(-·) is even, and D^(psi) = 0 for every primitive psi (odd psi:
  D is even; even psi: D^ = 2P^ = 0). By the proof of lem:splitF, D is split
  along (K_p)_{p | e*} on every coset of H*.
* G = Z + Y - Y(2·) + P - P(2·) has G^(chi) = 0 for every primitive chi:
  for odd chi this is (R1); for even chi, Z^ = Y^ = 0 and
  G^ = (1 - chi(2)) P^ = 0 by (R2). So G is split on every coset of H*.
* e* > 1: for e* = 1 all odd parts are 1, generation gives M = 4, and (R2)
  at conductor 4 reads mult(M/4) = mult(3M/4); with no pair, N_x = 0.

### 13.2 Moves at J = 2 (proved)

Each of the following leaves the elements of order larger than 4e* in place
and lowers the number of elements of order 4e*, or keeps it and lowers the
number of order 2e*; so it lowers the profile.

* (b) T-pairs. x_{+,v}, x_{-,v} in A: with S = {x, x + M/2} in T(x),
  A'' = A - x_{+,v} - x_{-,v} + y_v + M/2. y_{2v}, z_v in A:
  A'' = A - y_{2v} - z_v + z_{2v} + M/2.
* (c) a with -2a. x_{±,v} and y_{-v} = -2x in A: S = {x, -2x} in T(x),
  A'' = A - x - y_{-v} + (-x + M/2) + M/2 (one element of order 2e* fewer,
  the same number of order 4e*). y_v and z_{-v} = -2y_v in A:
  A'' = A - y_v - z_{-v} + z_{-v/2} + M/2.
* (d) y_v and y_{2v} in A: -2y_v = z_{-v} = -y_{2v} + M/2, and
  A'' = A - y_v - y_{2v} + z_{2v} + z_{-v/2} satisfies
  A'' + T(y_{2v}) + T(y_v) = A + pairs.
* Fibre moves (lem:movecrit). For q | e*, the elements x_{+,w} with w on a
  line vK_q are elements of order 4e* of one fibre Phi_q(x_{+,v}) (their
  differences are (M/4e*) times multiples of 4e*/q); likewise for x_{-,w},
  y_w, and z_w (for z only when e* != q). So no line along K_q carries
  (q + 1)/2 distinct elements of one type.

From now on none of these applies. Two sign facts follow.

* (i) P(v) and P(-v) never have opposite signs: P(v) >= 1 > 0 > P(-v) means
  x_{+,v}, x_{-,v} in A, and P(v) < 0 < P(-v) means x_{-,-v}, x_{+,-v} in A,
  T-pairs. So |D(v)| = |P(v)| + |P(-v)|, the mass of D is 2N_x <= 12, and
  D != 0; where P(v) != 0 it has the sign of D(v).
* (ii) Z(w), Y(w), -Y(2w) never have opposite signs ((c) for y_{±w} with
  z_{∓w}, (b) for z_{±w} with y_{±2w}, (d) for y_{±w} with y_{±2w}). So
  |Z + Y - Y(2·)|(w) = |Z(w)| + |Y(w)| + |Y(2w)|, and Z + Y - Y(2·) has mass
  2N_z + 4N_y.

Replacing A by -A changes the sign of P, D and G; so we may fix the sign of
one nonzero value of D.

### 13.3 The even core (proved)

**Lemma E.** D is of one of three shapes:

* I: D = sigma(1_L + 1_{-L}), sigma = ±1, L != -L a line along K_q with
  |K_q| <= 6 (q = 5, or q = 7 with 7 || e*);
* II: e* = p is prime and D is constant;
* III: e* = 35 and N_x = 6.

Proof. Lemma S and lem:grid apply to the K_p (Section 6). Let C be a coset
of H* on which D does not vanish; nonzero split functions have mass >= 4.

* Case (a), -1 not in H*. C and -C are distinct with the same mass (D is
  even), so D has mass <= 6 on C, and by lem:grid D = sigma 1_L on C, L a
  line along some K_q with |K_q| <= 6; by evenness D = sigma 1_{-L} on -C.
  These carry mass 2|L| >= 8, so D vanishes on every other coset: shape I.
* Case (b1), -1 in H* and e* = p prime. H* = K_p = U* and D is constant
  (S4): shape II. (For e* = p^k, k >= 2, -1 is not in H* = K_p.)
* Case (b2), -1 in H*, at least two primes. Take K = K_p of largest order,
  slices S_c = x c H' (c in K, H' the product of the other K_q), and write
  -1 = eps eps' with eps in K, eps' in H'; eps != 1 != eps' by lem:Kp(b).
  Since D(z eps eps') = D(-z) = D(z), multiplication by eps eps' maps S_c
  onto S_{c eps} and mu(c eps) = mu(c).
  - (i) Some slice vanishes. By (S2) D is split along H' on every slice. A
    nonzero slice S_c has mu(c) = mu(c eps) <= 6, and by lem:grid D = sigma
    on a line L along some K_q (q != p, |K_q| <= 6) in S_c and 0 elsewhere
    on S_c; on S_{c eps}, D = sigma on L eps eps' = -L. This uses mass
    2|L| >= 8, so no other slice or coset is nonzero: shape I.
  - (ii) All slices nonzero, mu(c_s) = 1 for some c_s. Then mu(c_s eps) = 1,
    and z -> D(z) - D(z eps) on S_{c_s} is split along H' of mass <= 2, hence
    0. If z_0 is the support point in S_{c_s}, the points z_0 eps and
    z_0 eps eps' of S_{c_s eps} both carry D(z_0) != 0, so they coincide and
    eps' = 1. Contradiction.
  - (iii) All mu(c) >= 2. Then 2|K| <= 12, so every |K_q| <= 6 and the primes
    of e* are 5 and 7. If 25 | e*, then |K_5| = 5 and eps in K_5 with
    eps^2 = 1 (from eps^2 eps'^2 = 1 and K_5 ∩ K_7 = 1) gives eps = 1; so
    e* = 35, |K| = 6, every mu(c) = 2 and the mass is 12 = 2N_x: shape III. ∎

### 13.4 Shape I: the compound move (proved)

Take sigma = 1. By (i), P = 1_S where S ⊂ L ∪ -L contains exactly one of
v, -v for each v in L, and N_x = |L|; all elements of order 4e* are x_{+,w},
w in S. By the fibre moves, S ∩ L and S ∩ -L have at most (q - 1)/2 points
each. If 25 | e*, |L| = 5 > 2 + 2; so q || e*, |L| = q - 1, and both have
exactly (q - 1)/2 points.

Let x = x_{+,v_0} with v_0 in S ∩ L, and apply sigma_{q,x}: Phi_q(x) consists
of the x_{+,w}, w in L, and one element x_0 of order 4e*/q. With
S' = {x_{+,w} : w in S ∩ L},

  A'' = A - S' + {-x_{+,w} : w in L \ S} + {-x_0, qx}.

For w in L \ S we have -w in S, and -x_{+,w} = x_{-,-w} = x_{+,-w} + M/2, so
A'' contains the (q - 1)/2 T-pairs {x_{+,u}, x_{-,u}}, u in S ∩ -L. The
T-moves replace each by {y_u, M/2}. The result,

  A - {x_{+,w} : w in S} + {y_u : u in S ∩ -L} + ((q - 1)/2) M/2 + {-x_0, qx},

has 8 elements, among them at least two copies of M/2; removing one pair
leaves at most 6 elements (4 if x_0 is in A), with no element of order 4e*
and none of larger order that A did not have. The chain is direct or
lowering (lem:transfer).

### 13.5 Shape II: prime e* (proved)

Take D = c > 0 constant on U* = (Z/p)^x. By (i), 0 <= P(v) <= c and
P(v) + P(-v) = c. The w with P(w) >= 1 index distinct elements x_{+,w} on the
line U* along K_p; by the fibre moves there are at most (p - 1)/2 of them, one
for each pair ±v at least. So P = c 1_S with S a set of representatives of
U*/±1, and N_x = c(p - 1)/2 <= 6.

* c >= 2. The move sigma_{p,x}, x = x_{+,v_0}, v_0 in S, works as in 13.4:
  Phi_p(x) is the x_{+,w}, w in U*, and one element x_0 of order 4; the
  T-pairs {x_{+,u}, x_{-,u}}, u in S, appear and the result is
  A - 2{x_{+,u} : u in S} + {y_u : u in S} + ((p - 1)/2) M/2 + {-x_0, px},
  with 8 elements, at least two copies of M/2, and fewer elements of order 4p.
* c = 1. G is constant on U* (S4) and sum_v G(v) = 0 (Z, Y odd;
  sum P = sum P(2·)), so G = 0. With psi = 1_S - 1_{-S},
  P(2·) - P = (psi(2·) - psi)/2, so

    Z + Y - Y(2·) = (psi(2·) - psi)/2,

  which takes the value 1 exactly on F = {w : w not in S, 2w in S}, -1 on -F,
  and 0 elsewhere. If y_v is in A, then (ii) gives (Z + Y - Y(2·))(v) >= 1,
  so v is not in S, -v is in S, and x_{+,-v} with y_v = -2x_{+,-v} is a move
  (c). So N_y = 0, Z = 1_F - 1_{-F}, and the elements of order p are the z_w,
  w in F, each once: N_z = |F|. The function psi along the cycles of w -> 2w
  on (Z/p)^x changes sign 2|F| times, and (p - 1)/2 + |F| <= 6.
  - p = 5: one 4-cycle with -1 = 4 = 2^2; the number of sign changes is
    twice an odd number and at most 4, so |F| = 1. Up to units, S = {1, 2},
    F = {3}: (a) {x_{+,1}, x_{+,2}, z_3} and three low elements.
  - p = 7: two 3-cycles {1, 2, 4}, -{1, 2, 4}; |F| = 0 or 2. Up to units,
    (c) S = {1, 2, 4}: {x_{+,1}, x_{+,2}, x_{+,4}} and three low elements;
    (e) S = {1, 2, 3}, F = {4, 5}: {x_{+,1}, x_{+,2}, x_{+,3}, z_4, z_5} and
    one low element.
  - p = 11: one 10-cycle with -1 = 2^5; the number of sign changes is twice an
    odd number, so |F| = 1, and psi is +1 on five consecutive powers of 2.
    Up to units S = {1, 2, 4, 8, 5}, F = {6}: (g)
    {x_{+,1}, x_{+,2}, x_{+,4}, x_{+,8}, x_{+,5}, z_6}.
  - p = 13: (p - 1)/2 + |F| >= 6 + 1. Impossible.

"Up to units" uses the units t ≡ 1 mod 4 of Z/M, which act on U* through all
of (Z/p)^x and keep the types x_+, x_-.

### 13.6 Shape III (proved)

Here N_x = 6, so Z = Y = 0 and G = P - P(2·), G^ = (1 - chi(2)) P^ for every
primitive chi mod 35. For chi = chi_5 chi_7 with both factors nontrivial,
chi_5(2) has order 2 or 4 (2 generates (Z/5)^x) and chi_7(2) has order 1 or 3
(2 has order 3 mod 7), so chi(2) != 1. Hence P^ = 0 at every primitive
character, P is split on U* = H*, nonzero, of mass 6, and by lem:grid
P = sigma 1_L with L a line along K_7: six distinct elements of one type
x_{+,w} (or x_{-,-w}) on one line along K_7, a fibre move. Contradiction.

### 13.7 J >= 3 (proved)

The elements of order 2^J e* are x_{t,v} = (M/2^J e*)u with
u ≡ t mod 2^J, u ≡ v mod e*, (t, v) in (Z/2^J)^x × U*. Put
F~(t, v) = mult(x_{t,v}) - mult(x_{-t,-v}). By lem:charstep and lem:splitF at
the order 2^J e* (no element has a larger order divisible by it), F~ is split
along K~_2 = {1, eta} × {1}, eta = 1 + 2^{J-1}, and the K_p. As
x_{t,v} + M/2 = x_{t eta, v}, the T-pairs are {x_{t,v}, x_{t eta,v}}.

Suppose A has no T-pair among these. The function
g(t, ·) = F~(t, ·) - F~(t eta, ·) is split along (K_p) on every coset of H*
(S1). For the orbit O = {t, t eta, -t, -t eta} (four elements, as J >= 3),
the four elements x_{t,v}, x_{t eta,v}, x_{-t,-v}, x_{-t eta,-v} form a
square of pairs and T-pairs, so A contains at most one of them or a diagonal,
and |g(t, v)| is the number of elements of A among them. Summing over v,
the mass of g(t, ·) is the number of elements of A of order 2^J e* with
first coordinate in O. Since a nonzero split function has mass >= 4 and
N_x <= 6, exactly one orbit O is occupied, and g(t_0, ·) = sigma 1_L with L a
line along K_q, |L| = N_x <= 6 (lem:grid). Replacing t_0 by t_0 eta we may
take sigma = 1: for v in L exactly one of x_{t_0,v}, x_{-t_0 eta,-v} lies in
A, once, and nothing else of order 2^J e*. The x_{t_0,v} lie on one fibre
line and the x_{-t_0 eta,-v} on another, so by the fibre moves each set has at
most (q - 1)/2 elements; hence q || e*, |L| = q - 1 and both have
(q - 1)/2 elements. The move sigma_{q,x}, x = x_{t_0,v_0} in A, produces
-x_{t_0,w} = x_{-t_0,-w} for the w in L with x_{t_0,w} not in A, and these
form T-pairs with the x_{-t_0 eta,-w} in A. As in 13.4 the T-moves leave at
most 6 elements, none of order 2^J e*. For e* = 1, g = 0 (an empty family),
so a T-pair always exists.

So at J >= 3 there is always a direct or lowering chain.

### 13.8 The global step (proved)

Let M be even, prime to 3, 4 | M, and suppose A has no move or chain. Every
maximal odd part e* has J >= 1 (Section 1); J = 1 gives a move (Section 11,
as M is not 70 or 110), J >= 3 a chain (13.7). So every maximal odd part has
J = 2, and by 13.4-13.6 its elements of odd part e* form, up to units and
sign, one of (a)_5, (c)_7, (e)_7, (g)_11, of sizes 3, 3, 5, 6.

* Two maximal odd parts. Sizes 3 + 3 with different odd parts: (a)_5 and
  (c)_7, so A lies in the subgroup of order 140 and M = 140.
* One maximal odd part e* in {5, 7, 11}. The low elements have odd part 1. If
  the largest 2-power order among them is 2^K with K >= 3, then eq:charrel at
  conductor 2^K involves only these elements (2^K does not divide 4e*), their
  odd counting function on (Z/2^K)^x has vanishing transform at every
  primitive character, and the others are trivial on {1, 1 + 2^{K-1}}; so it
  is invariant under multiplication by 1 + 2^{K-1}, and an element a of
  order 2^K comes with a + M/2: a T-pair, whose T-move lowers the profile.
  So the low elements lie in {M/4, M/2, 3M/4}, A lies in the subgroup of
  order 4e*, and M = 4e* in {20, 28, 44}.

The finite check. Balance at t = 1 says that the representatives in
[1, M - 1] add up to 3M.

* M = 20, (a) = {1, 17, 12}: the three low elements in {5, 10, 15} must add
  up to 30: {5, 10, 15} or {10, 10, 10}, both with a pair.
* M = 28, (c) = {1, 9, 25}: the low elements in {7, 14, 21} must add up to
  49: {7, 21, 21} or {14, 14, 21}, both with a pair.
* M = 28, (e) = {1, 9, 17, 16, 20}: the low element is 21, and
  A = {1, 9, 16, 17, 20, 21} is balanced. T(1) = {1, 15, 26, 14} gives
  {2, 9, 13, 14, 16, 17, 20, 21}, and T(6) = {6, 20, 16, 14} then gives
  {2, 9, 13, 17, 21, 22} = {2, 9, 17} ∪ {13, 21, 22}, a split sextuple
  (2 + 9 + 17 = 28, 13 + 21 + 22 = 56). So A is algebraic.
* M = 44, (g) = {1, 13, 37, 41, 5, 24}: the sum is 121, not 132.
* M = 140, (a)_5 ∪ (c)_7: up to units, {7, 119, 84} with {5, 45, 125} or
  {55, 75, 115} (the two signs of (c)); the sums are 385 and 455, not 420.

**Theorem (M prime to 3).** Let M be even and prime to 3, M not 70 or 110.
Every sextuple at level M has a direct or lowering move, or a chain of moves
to at most four elements, to six elements of lower profile or lower level, or
to a split sextuple. Hence, by induction on (M, profile), with
e84hc Theorem B for odd degrees and Peterson's theorem for degree 70, the
Hodge conjecture holds for the Fermat fourfold X^4_M whenever 3 ∤ M and
110 ∤ M.

## 14. Multiples of 6 and the exceptional degrees: open

For 3 ∤ M everything is closed except the multiples of 110 (Section 13).
For 3 | M, K_3 has order 2 or 3 and lem:grid fails, so Sections 2-13 do not
apply as they stand. The computations of Section 12 leave, up to 400, the
residual degrees 60, 66, 78, 84, 114, 132, 156, 168, 210 (and 330, a multiple
of 110); these have the Hodge conjecture by known theorems (Aoki for
2^a 3^b 5^c 7^d with c = 0 or d = 0; Peterson for 70, 140, 210; e84hc Theorem
A for 66, 78, 114, 132, 156). A hand argument for every multiple of 6 is to be
written.
