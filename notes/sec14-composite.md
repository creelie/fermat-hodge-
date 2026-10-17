# Section 14, local step at a composite e'

Status marks as in `even-degrees.md`: **proved** (hand proof here, or a
section of `even-degrees.md` that applies word for word), **checked** (finite
computation, script named), **open**. Scripts are in
`scratch-checks/forkC/` (working copies in `/dev/shm/tmpb/forkC`).

## C0. Setting and statement

e' is composite (at least two prime factors with multiplicity) and prime to 6,
D = 2^v 3^w divides 72, N = D e', U' = (Z/e')^x. As in `m6/locD.c`: an
*e'-element* is x in Z/N with gcd(x, e') = 1; a *local configuration* at level
N is a multiset B of at most six e'-elements with P' sum_{x in B} v_x = 0
(v_x(t) = (tx mod N), P' = prod_{p | e'} (|K_p| - sum_{k in K_p} R_k),
K_p = {t ≡ 1 mod N/p}), with no pair, no T-pair {x, x + N/2}, and no fibre
move: never (l + 1)/2 distinct elements of one order o, l | o, o != l, in one
fibre x + (N/l)Z, for l = 3 and l | e'.

A *local chain* (`scratch-checks/lchain.py`) is a sequence of moves with
sigma = T(y) = {y, y + N/2, -2y, N/2} or sigma_{l,y} = (y + (N/l)Z) ∪ {-ly}
(l = 3 or l | e'), sigma meeting the current multiset,
B_{i+1} = B_i - (sigma ∩ B_i) + (-(sigma \ B_i)) with pairs removed,
ending in at most |B| - 2 elements, or in at most |B| elements with the
largest order of the symmetric difference of the order multisets on the
removed side. The computations search chains of length at most 2; the hand
proofs below use longer ones.

**Coordinates.** For an e'-element x write x/N ≡ a/D + b/e' (mod 1), a in
Z/D, b in U'. Its *type* is d = D/gcd(a, D) (so ord x = d e'),
alpha = a/(D/d) in (Z/d)^x, and its *position* is y = d b in U'. Then
x <-> (alpha, y) for each type, units act diagonally, -x <-> (-alpha, -y).
The sigma_p fibre of x (p | e') meets the e'-elements of type d in the *line*
{(alpha, y k) : k in K_p}, where now K_p ⊂ U' is the kernel of
U' -> (Z/(e'/p))^x (|K_p| = p - 1 or p, lem:Kp); H = prod K_p.

**Theorem C.** For composite e' and D | 72, every local configuration at level
De' has a local chain, except at e' = 35 and e' = 55, where the configurations
without one are those of C13.

What is established:

* **proved**: C3-C9a: every configuration with D' ∈ {1, 2, 3}, with a
  maximal type 4, 8 or 9, or with maximal types {2, 3}, has a chain or does
  not exist, except the residuals at 35 (D' ∈ {1, 2, 3}, and one with D' = 6
  and maximal types {2, 3}) and 55 (D' = 2). (D' is the 2,3-part of the lcm
  of the orders of B, "type" as in the coordinates, maximal for divisibility.)
  What is left is case (R) of C10: every maximal type a multiple of 6.
* **proved**: C11.1: if every prime factor of e' is at least 29, every
  configuration is *formal*; C11.2: fork B's free-group description of the
  formal configurations holds modulo any such e'.
* **proved, given the checked free list** (Theorem 11.3): Theorem C, with no
  residual, for every composite e' with all prime factors at least 29 outside
  the exceptional set E_comp; **checked** (11.4): the 451 members of E_comp
  with all prime factors at least 29 (`comp/directc.log`). So Theorem C holds
  for every composite e' whose prime factors are all at least 29.
* **checked**: Theorem C for e' in {25, 35, 49, 55, 65, 77, 85, 91, 95, 115,
  119, 121, 125, 143, 175, 245, 275, 385} at the D | 72 of the table of C12,
  and for the further e' of C12 at D = 6, 12, 18 (`locG.c`, `lchain2.py`,
  `sweep.py`, `sweep2.py`).
* **open**: case (R) when some prime factor of e' is at most 23, at the e' and
  D not covered by the computation.

## C1. The relations at conductors f e' (proved)

Let f | D, f ≢ 2 mod 4, psi primitive mod f, and chi = psi chi' with chi'
primitive mod e', chi odd. For x in B of order d e', write x = (N/de') x' with
x' a unit mod de'; then x' ≡ alpha e' (mod d) and x' ≡ y (mod e'). The
elements of the global sextuple whose order is divisible by f e' are the x in B
with f | d (G0 of `sec14-global.md`; lem:charstep). Since
sum_{t mod n, unit} chi(t) B_1(tz/n) = chi̅(z) prod_{l | n, l ∤ c}(1 - chi(l))
B_{1,chi} for chi of conductor c | n, eq:charrel reads Γ̂_psi(chi') = 0, with
ĝ(chi') = sum_y g(y) chi̅'(y) and

  Γ_psi = sum_{x in B, f | d_x} (phi(D)/phi(d_x)) psi̅(alpha_x)
          prod_{l | d_x, l ∤ f} (1 - psi(l) T_l) delta_{y_x},

T_l delta_y = delta_{y/l} (so sum_x T_l delta_{y_x} = (sum_x delta_{y_x})(l ·)).
Only the part of Γ_psi of parity -psi(-1) is seen by the odd chi, so

**(Rel)** the part Γ_psi^par of Γ_psi of parity -psi(-1) is split along
(K_p)_{p | e'} on every coset of H (proof of lem:splitF).

Conversely the relations for all such (f, psi) are equivalent to
P' sum v_x = 0 (even chi give nothing). B is *formal* if every Γ_psi^par
vanishes identically. (`formal.py` writes psi(alpha) and psi̅(l): the
conjugate convention, the same set of relations.)

Each x contributes at most 2^{#{l in {2,3} : l | d, l ∤ f}} <= 4 points, so
|supp Γ_psi| <= 24 and |supp Γ_psi^par| <= 48.

**Top relation.** Let d_0 be a type of B maximal for divisibility with
d_0 ≢ 2 mod 4. At f = d_0 only the elements of type d_0 enter, without
product. With m(alpha, y) the multiplicity of the type-d_0 element (alpha, y)
and F(alpha, y) = m(alpha, y) - m(-alpha, -y), the relations for all primitive
psi mod d_0 say that F̂ vanishes at every primitive character of
(Z/d_0)^x × U' = (Z/d_0 e')^x, so F is split along
(K~_2, K~_3, (K_p)_{p | e'}) on (Z/d_0)^x × U', with
K~_l = {t ≡ 1 mod d_0/l} ⊂ (Z/d_0)^x (lem:Kp(c) for the modulus d_0 e'):

* K~_2 = {1, eta}, eta = 1 + d_0/2, for 4 | d_0: multiplication by eta is
  x -> x + N/2;
* K~_3 for 9 | d_0: the sigma_3 fibre x + (N/3)Z (all of type d_0);
* K~_3 for 3 || d_0: the swap of the two type-d_0 elements of that fibre.

As B has no pair, |F(alpha, y)| = m(alpha, y) + m(-alpha, -y) and the mass of
F is 2 N_{d_0} <= 12. Note that -1 lies in K~_2 K~_3 exactly for
d_0 ∈ {3, 4, 12}.

## C2. Split functions (proved)

Let K_1, ..., K_r have direct product H, C a coset of H, and f: C -> A split
along (K_1, ..., K_r), A any abelian group.

* **Support lemma.** If f != 0, then |supp f| >= min |K_i|. Induction on r:
  if some slice S_c (c in K_1) vanishes, f is split along (K_2, ..., K_r) on
  every slice (S2); otherwise every slice meets the support.
* **Support = min.** If |supp f| = m = min |K_i| and m >= 3, then f = c 1_L
  for a line L along some K_i with |K_i| = m. Induction on r: if a slice
  vanishes, exactly one slice is nonzero and the induction applies inside it.
  Otherwise |K_1| = m and each slice carries one point; for k in K_1,
  z -> f(z) - f(zk) on a slice is split along (K_2, ..., K_r) with support
  <= 2 < m, so it vanishes; f is K_1-invariant and its support is one line.
* **Line elimination.** If |supp f| < |K_1|, some slice vanishes and f is
  split along (K_2, ..., K_r) on every slice (S2).

Lemma S and lem:grid (`even-degrees.md` Section 6, e84hc) are used for the
K_p of U', which satisfy their hypotheses by lem:Kp.

## C3. Moves and the restriction to D' (proved)

**Filtered moves are chains.** A fibre move sigma_{p,x} with h >= (p + 1)/2
distinct elements of order o in the fibre (o != p) removes h of order o, adds
at most p - h of order o and two of order o/p: at most |B| elements, and the
net removed order o is the largest. A T-pair {x, x + N/2} with T(x) leaves
the size and removes the larger of the two orders (types 2^j d', checked case
by case: 4 | d, 2 || d, d odd). The moves (c) (x and -2x in B, 2 | ord x) and
(d) (x and 2x + N/2 in B) are chains of length one and two (`even-degrees.md`
Sections 3, 13.2).

**Restriction to D'.** If B lies in the subgroup of order D'e', D' | D, then B
is a configuration at level De' iff it is one at level D'e' (v_x(t) depends on
t mod ord x, and K_p at level De' maps onto K_p at level D'e'; for l = 2, 3,
x + N/l lies in the subgroup iff l | D', and then the filter is the one at
level D'e'). A chain at level D'e' is one at level De'
(x -> (D/D')x keeps T, sigma_l and orders). So the configurations at level De'
are those at the levels D'e', D' | D, and the residual set at D is contained in
the union of the residual sets at the D' | D, possibly smaller (at even D there
are T-moves that level D'e' lacks; example in C13).
(`bydp.py` checks that every L file at D carries the same forms of each
D' | D.)

## C4. D' = 1 (proved)

All elements have order e'. At f = 1 the odd part is F = m - m(-·), split,
of mass 2|B| <= 12, nonzero. By prop:core, either F >= 1 on a line wK_p with
p ∈ {5, 7}, i.e. |K_p| >= p - 1 >= (p + 1)/2 distinct elements of order
e' != p in one fibre, which the filter excludes; or e' = 35 with six elements
of order 35. So for composite e' != 35 there is no configuration with D' = 1.

## C5. D' = 2 (proved)

The types are 1 and 2, the only relation is f = 1, and it is the relation of
`even-degrees.md` Section 2 with e* = e' (positions: "E at v" has position
v/2, "F at v" position v). Sections 2-10 use only that relation, the moves
(b)-(d) (here (e), M/2 in B, cannot occur: B consists of e'-elements), the
fibre moves and N_e + N_{e*} <= 6; they apply word for word. So, unless
e' ∈ {35, 55}, E_1 is a non-cancelling line sum and Section 5 gives a chain.

Local size count for Section 5. Start with n = N_e + N_{e*} >= 1 elements
(N_e >= 1 as D' = 2). The N_e moves T(x) at the tops add 2 each and N_e copies
of N/2, of which eps = N_e mod 2 survive; the positive lines number at most
floor(s/4), s = N_{e*} + 2N_e, and each sigma_{p,y} leaves at most two
elements. The end has at most eps + 2 floor(s/4) <= n elements: for eps = 0
this is s/2 <= n; for eps = 1 and N_{e*} >= 2 it is 1 + s/2 <= n; for eps = 1
and N_{e*} ∈ {0, 1}, s ≡ 2, 3 mod 4 and 2 floor(s/4) = N_e - 1. It has no
element of order 2e' or e' (the lines are removed whole, the sigma moves add
orders e'/p), so the order 2e' is the largest of the symmetric difference, on
the removed side: an accepted chain.

At e' ∈ {35, 55}, Section 10 leaves the residuals of C13 (D' = 2).

## C6. A maximal type 8 (proved)

Let 8 be a maximal type (D | 72, so 8 = d_0, and no type 24 or 72 occurs).
`even-degrees.md` 13.7 applies with e* = e': the top relation of C1 is the one
used there, (Z/8)^x is one orbit {t, t eta, -t, -t eta}, and its proof gives,
for the q - 1 elements of type 8 (q || e', |K_q| = q - 1 <= 6), the chain
sigma_{q,x} followed by (q - 1)/2 moves T. Count: n - (q - 1)/2 + (q - 1)/2 + 2
after sigma, unchanged by the T-moves, with (q - 1)/2 >= 2 copies of N/2, one
pair of them removed: at most n elements. All type-8 elements are gone, the
new ones have orders 4e', 2, 8e'/q: accepted.

## C7. A maximal type 4 (proved)

Let 4 be a maximal type (no type 8, 12, 24, 36, 72). The top relation at
f = 4 is (R2) of 13.1, so D = P + P(-·) is split, and the sign fact (i) of
13.2 holds (a T-pair otherwise). Lemma E (13.3): shape II needs e' prime;
shape III needs N_4 = 6, so D' = 4, and 13.6 excludes it (its relation G is
the f = 1 relation with no elements of type 1, 2). Shape I: the chain of 13.4,
sigma_{q,x} and (q - 1)/2 moves T, ends with n + 2 - 2 = n elements (one pair
of N/2 removed) and no element of type 4: accepted.

## C8. A maximal type 9 (proved)

Let 9 be a maximal type (no 18, 36, 72). By C1, F is split along
(K~_3, (K_p)) on (Z/9)^x × U', K~_3 = {1, 4, 7}, and -1 ∉ K~_3. For
kappa ∈ {4, 7} and alpha in (Z/9)^x put g(·) = F(alpha, ·) - F(alpha kappa, ·),
split along (K_p) (S1). Its four terms involve the elements (alpha, y),
(-alpha, -y), (alpha kappa, y), (-alpha kappa, -y), with signs +, -, -, +; two
of opposite sign form a pair or lie in one sigma_3 fibre with the same type
(two of them: a fibre move). So g does not cancel and its mass is
n(±alpha) + n(±alpha kappa), n(±alpha) the number of type-9 elements with
first coordinate ±alpha. By the support lemma this is 0 or >= 4.

The three classes ±alpha are permuted cyclically by K~_3. With
n_9 = sum <= 6, either one class carries all, n_9 >= 4, or n(c) = 2 for all
three classes.

* One class ±alpha: F(alpha kappa, ·) = 0 and F(alpha, ·) is split of mass
  n_9 <= 6, so by lem:grid F(alpha, ·) = sigma 1_L, L a line along K_q,
  |K_q| <= 6: at least |K_q| >= (q + 1)/2 distinct elements (sigma alpha, y),
  y ∈ sigma L, in one sigma_q fibre. Excluded.
* (2, 2, 2): each g has mass 4, so g = sigma 1_L (lem:grid) without
  cancellation; then F(alpha, ·) is sigma on its two points and F(alpha kappa, ·)
  is -sigma on its two. The sign s(alpha) of F(alpha, ·) satisfies
  s(4 alpha) = s(7 alpha) = -s(alpha), but 4 · 4 = 7 gives
  s(7 alpha) = s(alpha). Contradiction.

So no configuration has a maximal type 9 (agrees with the data: `maxtypes.py`).

## C9. D' = 3 (proved)

Types 1 and 3; Z+, Z- the type-3 elements with alpha = 1, -1, E the type-1
elements. Relations:

* f = 3, psi = chi_3: Z^e = Q + Q(-·) is split, where
  Q(y) = mult(Z+ at y) - mult(Z- at -y);
* f = 1: G = 2E + Z^o - Z^o(3·) is split, where E(y) = m_1(y) - m_1(-y) and
  Z^o = (Z+ + Z-) - (Z+ + Z-)(-·).

Q(y) and Q(-y) never have opposite signs (Z+ and Z- at one position lie in one
sigma_3 fibre: a fibre move), so Z^e has mass 2N_3 and is nonzero. Lemma E
gives shape I, II (e' prime, excluded) or III (e' = 35, N_3 = 6). In shape I,
after replacing B by -B, Z^e = 1_L + 1_{-L}, all type-3 elements are Z+ at the
points of a set S containing one of ±v for each v ∈ L, and by the sigma_q
filter q || e', |L| = q - 1 and |S ∩ L| = |S ∩ -L| = (q - 1)/2. Put
psi_S = 1_S - 1_{-S}; then Z^o = psi_S and G = 2E + psi_S - psi_S(3·).
For composite e', -1, 3, -3 ∉ K_q (they are not ≡ 1 mod e'/q), so
L, -L, L/3, -L/3 are four distinct lines.

**q = 7.** N_3 = 6, E = 0. Let C be the H-coset of L. If one of the four lines
is not in C, then for k ∈ K_7 the function h(z) = G(z) - G(zk) on each coset of
H' = prod_{p != 7} K_p in C has support <= 3 < min |K_p|, so G is
K_7-invariant on C; but G = psi_S on L takes the values 1 and -1. So all four
lines lie in C. Choose y ∈ L, k ∈ K_7 with psi_S(y) != psi_S(yk); h is
nonzero at y, and on the H'-coset of y its support is at most the four points
where it meets the four lines. By the support lemma it is exactly these, by
support = min they form one line along K_5 (|K_5| = 4, 5 || e'). Hence -1 and
3 lie in K_5 K_7, i.e. are ≡ 1 mod e'/35, and e' = 35.

**q = 5, e' = 5m squarefree.** U' = (Z/5)^x × (Z/m)^x, K_5 = (Z/5)^x × 1,
L = (Z/5)^x × {z_0}, all |K_p| >= 6 for p | m, N_3 = 4, N_1 <= 2. Write
s(c) = psi_S(c, z_0), two values +1 and two -1. On the four special
z ∈ (z_0, -z_0, z_0/3, -z_0/3) the function G - 2E restricted to the slice
{c} × (Z/m)^x is

  Psi(c) = (s(c), -s(-c), -s(3c), s(-3c)),  i.e.
  Psi(2^i) = (s_i, -s_{i+2}, -s_{i+3}, s_{i+1}), s_i = s(2^i),

and 0 elsewhere. For c, c' the function D_{c,c'} = G(c, ·) - G(c', ·) is split
along (K_p)_{p | m} (S1), so it vanishes or has support >= 6, and support
exactly 6 makes it constant on a line along K_7. With two + and two -, s is
*adjacent* (s_{i+2} = -s_i, Psi(2^i) = (s_i, s_i, s_{i+1}, s_{i+1}),
Psi(-c) = -Psi(c)) or *alternating* (s_{i+2} = s_i,
Psi(c) = s(c)(1, -1, 1, -1), Psi(-c) = Psi(c)).

* N_1 = 0: every D_{c,c'} has support <= 4, so vanishes, and Psi is constant:
  but s is not.
* E supported on the two slices ±c_1 (this covers N_1 = 1, and N_1 = 2 with
  the elements in slices ±c_1, multiplicity 2 included): D_{2c_1, -2c_1} =
  Psi(2c_1) - Psi(-2c_1) has support <= 4, so vanishes: s is alternating.
  Then D_{c_1, 2c_1} = 2s(c_1)(1, -1, 1, -1) + 2E(c_1, ·), where E(c_1, ·)
  has at most two points: it is nonzero, so its support is exactly 6, with
  both E-points off the special z, and then it takes both values ±2 on the
  special z: not constant. Contradiction.
* N_1 = 2 with E on all four slices, one point e_c delta_{z_c} on each:
  adjacent: for each i the special part of D_{2^i, 2^{i+1}} has support 2
  (on {±z_0} if s_i != s_{i+1}, on {±z_0/3} if s_i = s_{i+1}), the total
  support is <= 4, so it vanishes, which forces z_{2^{i+1}} into that pair.
  Since s_i = s_{i+1} implies s_{i+1} != s_{i+2}, some slice is forced into
  both pairs. Alternating: D_{c, -c} = 2e_c(delta_{z_c} + delta_{-z_c})
  (oddness of E, Psi(-c) = Psi(c)), nonzero of support 2. Contradiction.

**q = 5, e' not squarefree.** Then R = prod_{p^2 | e'} p^{v_p - 1} >= 7,
H = {u ≡ 1 mod R}, and -1, 3, -3 ∉ H, so L, -L, L/3, -L/3 lie in four
distinct H-cosets. On vH (v ∈ L), G = 2E + psi_S; each H'-coset of vH meets L
once, so for k ∈ K_5, z -> G(z) - G(zk) has support <= 1 + 4 < 6 there and
vanishes: G is K_5-invariant on vH, and s(c) + 2E(vc) is constant on L. As s
takes both signs, E is nonzero at two points of L at least. The same on
(v/3)H, with -psi_S(3·): two points of L/3. With oddness, E has at least eight
points, but at most four (N_1 <= 2). Contradiction.

So for composite e' != 35 there is no configuration with D' = 3. (At e' = 35
the residuals of C13 with D' = 3 are all of type 3: shape III or q = 7.)

## C9a. Maximal types {2, 3} (proved)

Let the maximal types be 2 and 3, so the types are 1, 2, 3 (n_1, n_2, n_3
elements, n_2, n_3 >= 1) and D' = 6. The relations are f = 3 and f = 1.

* f = 3: only type 3 enters, so Z^e = Q + Q(-·) is split, exactly as in C9.
* f = 1 (weights phi(6)/phi(d) = 2, 2, 1): G = A + psi_S - psi_S(3·) is
  split along (K_p)_{p | e'} on every coset of H, where
  A = 2E + 2Y - 2Y(2·), E(y) = m_1(y) - m_1(-y), Y(y) = m_2(y) - m_2(-y)
  (m_d(y) the multiplicity of the type-d element at y; Z^o = psi_S as in C9).

**Step 1 (as in C9).** Lemma E for Z^e: shape II needs e' prime, shape III
needs n_3 = 6 (no room for type 2). In shape I, after B -> -B, q || e',
n_3 = q - 1 <= 5, so q = 5, 5 || e', n_3 = 4, n_1 + n_2 <= 2, all type-3
elements are Z+ at S, |S ∩ L| = |S ∩ -L| = 2 for the K_5-line L, and psi_S
takes the values +1, +1, -1, -1 on L. A type-2 element at y gives A the
values 2, -2, -2, 2 at y, -y, y/2, -y/2, a type-1 element 2, -2 at y, -y; so
A is even-valued with |supp A| <= 8, and |supp A| = 8 only if n_2 = 2,
n_1 = 0 and nothing cancels. The points ±z_0, ±z_0/3 (z_0 ∈ L) have pairwise
ratios in {±1, ±3, ±1/3}.

**Step 2: e' not squarefree.** Some p >= 7 has p^2 | e', so
R = prod_{p^2 | e'} p^{v_p - 1} >= 7, H = {u ≡ 1 mod R}, and -1, ±3 ∉ H:
the cosets vH, -vH, (v/3)H, (-v/3)H (v ∈ L) are distinct. On vH,
G = A + psi_S with psi_S supported on L; on (v/3)H, G = A - psi_S(3·) with
psi_S(3·) supported on L/3, again with values +1, +1, -1, -1. Let alpha, beta
be the numbers of points of supp A in vH and in (v/3)H.

* alpha, beta >= 1: if alpha = 0, G on vH has support L, of size
  4 = |K_5| = min |K_p|, so by support = min it is constant on L; but psi_S
  is not. The same for beta. By oddness |supp A| >= 2 alpha + 2 beta, so
  alpha + beta <= 4 and alpha, beta <= 3.
* For k ∈ K_5, z -> G(z) - G(zk) on an H'-coset of vH (H' = prod_{p != 5} K_p,
  all |K_p| >= 6) is split along (K_p)_{p != 5} and has support at most
  1 + alpha <= 4 (the coset meets L once), so it vanishes: G is K_5-invariant
  on vH. Off L, G = A is then a union of K_5-lines (4 points each), so empty;
  on L, A = c - psi_S with c odd, nonzero at 2 or 4 points. So alpha = 2 and
  supp A ∩ vH ⊂ L; likewise beta = 2 and supp A ∩ (v/3)H ⊂ L/3.
* Hence |supp A| = 8, n_2 = 2, n_1 = 0, and every point of
  supp A = {±y_j, ±y_j/2} (y_1, y_2 the type-2 positions) lies in the four
  cosets. As y_j/(y_j/2) = 2, 2 ∈ {±1, ±3, ±1/3}H, i.e. R divides one of
  1, 3, 1, 5, 5, 7; as 5 ∤ R (5 || e'), R = 7 and -6 ∈ H. Modulo 7 the four
  cosets are v·{1, 6, 5, 2} and division by 2 is multiplication by 4, so
  y_j ∈ ±(v/3)H and y_j/2 ∈ ∓vH. Each j gives one point p_j ∈ L
  (= ∓y_j/2) and one point q_j ∈ L/3 (= ±y_j) with p_j = -q_j/2; then p_j
  and 3q_j are two points of the K_5-line L with ratio -1/6, so -6 ∈ K_5,
  i.e. e'/5 | 7, against 49 | e'.

**Step 3: e' = 5m squarefree, m != 7.** U' = (Z/5)^x × (Z/m)^x,
K_5 = (Z/5)^x × 1, L = (Z/5)^x × {z_0}, and the special points ±z_0, ±z_0/3
of (Z/m)^x are distinct. As in C9, on the slice {c} × (Z/m)^x,
G(c, ·) = A(c, ·) + Psi(c) with Psi(c) = (s(c), -s(-c), -s(3c), s(-3c)) on
the special points and 0 elsewhere, s(c) = psi_S(c, z_0) (two values +1, two
-1). The four points of a type-2 element lie in four different slices
(-1, ±2 ≢ 1 mod 5), so each A(c, ·) has at most two points, and
D_{c,c'} = G(c, ·) - G(c', ·), split along (K_p)_{p | m}, has support <= 8.

* If every p | m is at least 11 (|K_p| >= 10), D_{c,c'} = 0 by the support
  lemma.
* If 7 | m, m = 7m'' with m'' > 1: line elimination along the K_p, p | m''
  (support 8 < 10), leaves D_{c,c'} constant on every K_7-coset, a union of
  K_7-lines of 6 points. A K_7-line holds at most one special point (-1, ±3,
  ±1/3 are not ≡ 1 mod m''), so it would need 5 points from A, which gives
  D at most 4. So D_{c,c'} = 0.

So G(c, ·) = K does not depend on c and A(c, z) = K(z) - Psi(c)(z). At each
special z the value Psi(c)(z) takes each sign for two c, and K(z) is odd, so
A has at least two points at each special z: at least 8, so exactly 8, all
special, n_2 = 2, n_1 = 0. Then y_j and y_j/2 are both special in the
(Z/m)^x-coordinate, 2 ∈ {±1, ±3, ±1/3} mod m, so m divides one of 1, 3, 1, 5,
5, 7: m = 7, excluded.

So for composite e' != 35 no configuration has maximal types {2, 3}; the moves
(c), (d) are not needed. (At e' = 35, m = 7, neither bullet of Step 3 applies
(|K_7| = 6 <= 8), and the data, `maxtypes.py`, has exactly one configuration with maximal types
{2, 3}: the residual {2, 26, 86, 111, 152, 153} of C13, types 3, 3, 3, 2, 3,
2.)

## C10. Reduction (proved)

The maximal types form an antichain of divisors of 72 with lcm D'. By C4-C9a,
a configuration with no chain, outside the residuals at 35 and 55, has
D' ∉ {1, 2, 3}, no maximal type 4, 8, 9, and maximal types other than
{2, 3}. So:

**(R)** every maximal type is a multiple of 6: the maximal types are {6},
{12}, {18}, {24}, {36}, {72}, {12, 18}, {18, 24} or {24, 36}.

In the data (`maxtypes.py`) the maximal type sets that occur are {1}, {2},
{3}, {4}, {8} (these with chains, outside 35 and 55), {2, 3} (only at 35),
{6}, {12}, {18}, {24}, {36}, {72}; never {9}, and never two maximal types
except {2, 3} at 35.

## C11. Large primes: the formal regime

**Proposition 11.1 (proved).** If |K_p| >= 25 for every p | e' (e.g. every
prime factor at least 29), every configuration is formal: every Γ_psi^par
vanishes identically.

Proof. Let g = Γ_psi^par, split along (K_p), with g(-y) = ±g(y),
supp g ⊆ S ∪ -S, S = supp Γ_psi, |S| <= 24.
If e' is not squarefree, -1 ∉ H (H = {u ≡ 1 mod R}, R >= 5), and on a coset C,
supp g ∩ C ⊆ (S ∩ C) ∪ -(S ∩ -C) has at most 24 < min |K_p| points: g = 0 by
the support lemma. If e' is squarefree (two primes at least), H = U'; take
K = K_p of largest order, slices S_c, -1 = eps eps' with eps ∈ K,
eps' ∈ H' = prod_{q != p} K_q, both != 1 (lem:Kp(b), and -1 ∉ K_p as e' != p).
Multiplication by -1 maps S_c onto S_{c eps} and preserves |g|. If a slice
vanishes, g is split along H' on every slice, and a nonzero slice S_c and
S_{c eps} carry >= 2 · 25 > 48 points. Otherwise, as 48 < 2|K|, some S_{c_s}
has one point z_0, and so has S_{c_s eps}; z -> g(z) - g(z eps) on S_{c_s} is
split along H' with support <= 2, hence 0, so g(z_0 eps) = g(z_0) != 0 and
g(z_0 eps eps') = ±g(z_0) != 0 are both in S_{c_s eps}: eps' = 1, a
contradiction (the argument of lem:oddbig). ∎

**11.2 Fork B's formal regime at a composite modulus (proved).** When every
Γ_psi^par vanishes, the configuration condition is the system of point
conditions of `sec14-prime.md` Q1 with all constants zero, with (Z/p)^x
replaced by U' = (Z/e')^x: for each layer c | D, c ≢ 2 mod 4, and each class
{±v} ⊂ U', P_c omega_c(·, v) = 0 (the Γ_psi, psi primitive mod c, are the
P_c-components of omega_c). If every prime factor q of e' is at least 29, a
sigma_q fibre move needs (q + 1)/2 >= 15 elements, so the filters are those of
Q0 (pair, T-pair, sigma_3). Q3, Q4 and Q6 then hold word for word with p
replaced by e': they use arithmetic in U' with 2 and 3 invertible, and never
that p is prime. So:

(a) a configuration without a proper sub-configuration is connected and, after
    a unit, lies in the coset <-1, 2, 3> of 1; along a spanning tree it lifts to
    the free group. If e' is not in

      E_comp = {e' : 2^a 3^b ≡ ±1 mod e' for some (a, b) != (0, 0),
                |a| <= 18, |b| <= 12},

    reduction is injective on the points of the lift (Q6), so B is the
    reduction of one of the 16 formal configurations of `F_3_2.txt`; as these
    have at least 5 elements, every configuration with at most 6 elements is
    minimal.
(b) The chains of the 16 (`fdump/`, at level D_B, moves T and sigma_3 only)
    reduce to chains modulo e' (Q6(c)): the collision numbers of `CP.txt`
    (2^{a+} 3^{b+} ∓ 2^{a-} 3^{b-}, |a| <= 2, |b| <= 1) have no prime factor
    >= 29, so no such e' divides one, and the order comparison needs
    d e' > d' for d, d' | 72, true as e' >= 29^2. A move sigma_q, q | e',
    gives at least q + 1 - |b| > 12 elements from a multiset b of at most 12,
    so the chains with T and sigma_3 are all the local chains.
(c) The 16 have D_B ∈ {6, 12, 24}; by C3 the configurations at level De' are
    those with D_B | D, and their chains at level D_B e' are chains at level
    De'.

**Theorem 11.3 (proved, given the checked formal list).** Let e' be composite
with every prime factor at least 29, e' ∉ E_comp. Then for every D | 72 every
configuration at level De' has a local chain; there are none unless 6 | D,
and they are the reductions of the 8, 12 or 16 formal configurations with
D_B | D.

**11.4 The exceptional composites (checked).** The composite e' in E_comp with
every prime factor at least 29 are the composite divisors of the numbers
2^a 3^b ± 1, |2^a ± 3^b| (0 <= a <= 18, 0 <= b <= 12) built from primes
>= 29: 451 values from 841 to 69657034751 (`comp/candcomp.py 18 12`,
`comp/Ecomp.txt`). For each, `comp/directc.py` runs `propc 3 2 e'` (fork B's
prop.c with Euclid's inverse, so any modulus prime to 6; complete by Q4, since
11.1 gives the point conditions), compares with the reductions of the 16
(`specializec.py`) and searches chains at level D_B e' (`levelchainc.py` with
LEVEL=DB, backend `fchainc.py`, the moves T and sigma_3 of `lchain.py`):
for all 451 the configurations at level 72e' are exactly the reductions of
the 16 (no extra configuration, none missing), and each has a chain at level
D_B e' (`comp/directc.log`, 451 lines "extra 0 missing 0 | configs 16
nochain 0").

Cross-checks: `propc 3 2 29` equals fork B's `modp/P_3_2_29.txt`; at
D = 6, `propc 1 1 e'` gives 8 configurations at both e' = 841 (in E_comp)
and 899 = 29 31 (not), the 8 reductions with D_B = 6 (`comp/out/P_1_1_*.txt`);
the comparison with `locG e' 1 1` is queued in `sweep2.py`.

So Theorem C holds, with no residual, for every composite e' all of whose
prime factors are at least 29.

**Free model (checked, fork B).** `F_3_2.txt`: 16 formal configurations
(sizes 5 and 6), 8 with D_B = 6, 4 with D_B = 12, 4 with D_B = 24, each with a
chain of one or two moves T and sigma_3. In agreement, every composite e' of
C12 carries exactly 8 configurations with D' = 6, 4 with D' = 12, 4 with
D' = 24 that are formal (`formal.py` at D = 6: 8 formal at each of 25, 35,
..., 143).

**Top relation (proved, a first step for (R)).** If |K_p| >= 7 for every
p | e' (5 ∤ e', and 49 | e' if 7 | e'), the top relation is formal: for every
y, F(·, y) is split along (K~_2, K~_3). The proof is that of the proposition
with S the positions of the type-d_0 elements (|S ∪ -S| <= 12): a coset carries
at most 6 < 7 points if -1 ∉ H; if -1 ∈ H, a vanishing slice gives two nonzero
slices with 2 · 7 > 12 points, and otherwise 12 < 2|K| gives a slice with one
point. So the K_p-part of the top function can only come from 5 || e' or
7 || e'; in the data non-formal configurations occur only for 5 || e' (and at
25).

## C12. Computations (checked)

`locG.c` (same definitions, filters and output as `m6/locD.c`; usage
`locG e' v w`) lists all configurations. It is a meet in the middle on a
random 64-bit linear hash of P' v_x: a table of the sums over x_0 and at most
two further elements (x_0 the element of B whose order has the largest class
rank, one table per order), and an enumeration of the other side (at most
three elements). A configuration always gives a hash hit, and every hit is
verified by the exact sum, so the list is complete; canonical forms (lex-min
over the units) are deduplicated by a 64-bit hash, which could only drop a
configuration through a hash collision. `lchain2.py` (lchain.py with the
preimages of -2x and -lx solved directly; same moves, same acceptance,
depth 2) finds chains. `sweep.py` runs (e', D) for the 18 e' of the
directive and every D | 72 (D = 72 only for phi(e') <= 72; D = 24, 36 at
275 and 385 last), `sweep2.py` further e' at D = 6, 12, 18 (D = 12, 18 when
ne <= 2880); they write `data/L_v_w_e.txt` (configurations) and
`data/R_v_w_e.txt` (those without a chain), with timings in `sweep.log`,
`sweep2.log`; `table.py` prints the tables below. One core; the peak resident
memory of locG was 0.88 GB at ne = 5760 (e' = 385, D = 24) (ne = phi(e') D, the table has O(ne^2) entries).

Configurations found, with the number without a chain in brackets
("-": not run):

| e' | D=1 | D=2 | D=3 | D=4 | D=6 | D=8 | D=9 | D=12 | D=18 | D=24 | D=36 | D=72 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 25 | 0 | 4 | 0 | 4 | 13 | 4 | 0 | 17 | 13 | 21 | 17 | 21 |
| 35 | 2 (2) | 33 (7) | 4 (4) | 35 (7) | 59 (13) | 37 (7) | 4 (4) | 67 (13) | 63 (13) | 75 (13) | 73 (13) | 83 (13) |
| 49 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | 16 |
| 55 | 0 | 6 (2) | 0 | 8 (2) | 18 (2) | 10 (2) | 0 | 26 (2) | 22 (2) | 34 (2) | 32 (2) | 42 (2) |
| 65 | 0 | 4 | 0 | 6 | 16 | 8 | 0 | 24 | 20 | 32 | 30 | 40 |
| 77 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | 16 |
| 85 | 0 | 5 | 0 | 7 | 17 | 9 | 0 | 25 | 21 | 33 | 31 | 41 |
| 91 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 95 | 0 | 4 | 0 | 6 | 16 | 8 | 0 | 24 | 20 | 32 | 30 | - |
| 115 | 0 | 4 | 0 | 6 | 16 | 8 | 0 | 24 | 20 | 32 | 30 | - |
| 119 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 121 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 125 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 143 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 175 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | 12 | - |
| 245 | 0 | 4 | 0 | 6 | 16 | 8 | 0 | 24 | 20 | 32 | - | - |
| 275 | 0 | 0 | 0 | 0 | 8 | 0 | 0 | 12 | 8 | 16 | - | - |
| 385 | 0 | 4 | 0 | 6 | 16 | 8 | 0 | 24 | 20 | - | - | - |

Distinct configurations by D' (`bydp.py`, all files consistent with C3):

* 49, 77, 91, 119, 121, 125, 143, 175, 275: D' = 6: 8, 12: 4, 24: 4 (the 16
  formal ones of the free model).
* 25: D' = 2: 4, 6: 9, 12: 4, 24: 4.
* 65, 95, 115, 245, 385 (5 || e'): D' = 2: 4, 4: 2, 6: 12, 8: 2, 12: 6,
  18: 4, 24: 6, 36: 2, 72: 2 (65; D' = 72 not run elsewhere); 85: the same
  with 5 at D' = 2.
* 35: D' = 1: 2, 2: 31, 3: 2, 4: 2, 6: 24, 8: 2, 12: 6, 18: 4, 24: 6, 36: 2,
  72: 2. 55: D' = 2: 6, 4: 2, 6: 12, 8: 2, 12: 6, 18: 4, 24: 6, 36: 2, 72: 2.

The non-formal configurations at D = 6 (`formal.py`, files `fm_1_1_e.txt`;
counted as D' = 2 + D' = 6) are 4 + 4 at 65, 95, 115, 5 + 4 at 85, 4 + 1 at
25, none at 49, 77, 91, 119, 121, 125, 143. All those with D' = 6 carry a
move (c) (flag c = 1); those with D' = 2 carry (c) or (d); all have chains.

## C13. Residuals at 35 and 55 (checked)

Canonical forms (lex-min over the units) at level D'e' (`residforms.py`); a
residual at D' is a residual at every D with D' | D listed. Elements are
residues mod D'e'.

e' = 35:

| D' | level | B | orders | no chain at D in |
|---|---|---|---|---|
| 1 | 35 | {1, 2, 11, 16, 22, 32} | 35 (six) | every D |
| 1 | 35 | {1, 2, 16, 17, 22, 31} | 35 (six) | 1, 3, 9 only |
| 2 | 70 | {1, 2, 3, 43, 61, 62} | 70, 35, 70, 70, 70, 35 | every even D |
| 2 | 70 | {1, 2, 43, 44, 47, 61} | 70, 35, 70, 35, 70, 70 | every even D |
| 2 | 70 | {1, 3, 12, 52, 62, 62} | 70, 70, 35, 35, 35, 35 | every even D |
| 2 | 70 | {1, 4, 32, 44, 62} | 70, 35, 35, 35, 35 | every even D |
| 2 | 70 | {1, 24, 44, 52, 62} | 70, 35, 35, 35, 35 | every even D |
| 2 | 70 | {1, 24, 61, 62} | 70, 35, 70, 35 | every even D |
| 3 | 105 | {1, 4, 16, 46, 64, 79} | 105 (six) | 3 divides D |
| 3 | 105 | {1, 4, 46, 47, 64, 68} | 105 (six) | 3 divides D |
| 6 | 210 | {1, 17, 47, 143, 169, 173} | 210 (six) | 6 divides D |
| 6 | 210 | {1, 34, 44, 94, 187, 194} | 210, 105, 105, 105, 210, 105 | 6 divides D |
| 6 | 210 | {1, 79, 109, 121, 151, 169} | 210 (six) | 6 divides D |
| 6 | 210 | {2, 26, 86, 111, 152, 153} | 105, 105, 105, 70, 105, 70 | 6 divides D |

Counts per D: 2 (D = 1), 7 (D = 2, 4, 8), 4 (D = 3, 9), 13 (6 | D: one with
D' = 1, six with D' = 2, two with D' = 3, four with D' = 6). So the residuals
with 2,3-part dividing 6 are all of them, and none has D' with 4 | D' or
9 | D'. The second D' = 1 form gets a chain at even D (T-moves).

e' = 55: at every even D, two residuals with D' = 2, level 110:
{1, 24, 62, 71, 81, 91} (orders 110, 55, 55, 110, 110, 110) and
{1, 31, 71, 81, 91} (all 110); none at odd D.

These agree with `scratch-checks/glob/residuals_35.txt`, `residuals_55.txt`
and with the table of `sec14-global.md` G0.

## C14. What is open

* Case (R) of C10 (every maximal type a multiple of 6) when some prime factor
  of e' is at most 23, outside the computed (e', D). Two things are missing.
  Formality: the top relation is formal when every |K_p| >= 7 (C11), but the
  other relations need |K_p| >= 25 in Proposition 11.1; the computation finds
  non-formal configurations only for 5 || e' (and at 25), all with chains
  outside 35 and 55, all with a move (c) or (d). The free model at small
  primes: when B is formal but e' has a prime factor below 29, the marked
  group <-1, 2, 3> can have short relations modulo e', so 11.2(a) gives
  reductions of the free configurations only for e' ∉ E_comp, and the fibre
  filters at small q | e' enter; 11.2(b) still reduces the chains whenever
  e' has one prime factor at least 29 (e' then divides no collision number).
  The first non-formal case is D' = 6, with relations (R1)
  2E + 2(1 - T_2)Y + (1 - T_3)Z^o + (1 - T_2)(1 - T_3)X^o and (R3)
  Z^e + (1 + T_2)X^e (notation of C9, X, Y for types 6, 2), and no relation
  at 2e' or 6e'.
* Not run (sweep still running when this was written): D = 36 at 245, 275,
  385; D = 72 at 91, 95, and for phi(e') > 72; the `sweep2.py` list.
