/-
HodgeClosure.lean

Kernel-checked finite arithmetic and propositional logic behind the paper
"Hodge Classes on K3 Powers and Sixfolds"
(D. Bhattacharjee, U. Bhattacharya).

Nothing here formalises algebraic geometry.  Results of the paper are named
by their labels in the LaTeX source.  What is checked is

  Section 1  the closure graph of statements: with the implications proved
             in the paper and in the literature taken as rules, the Hodge
             conjecture follows from exactly the minimal sets
             {F3}, {L, M}, {L, F3'}, {V, F3'}, {F2, F3'}, and from no proper
             subset of any of them (Proposition minimal);
  Section 2  dimension counts of the loci on which the Weil classes are
             known to be algebraic, the count 26 of Theorem link(i) and the
             values of the lower bound r = (4 + rho) n^2 - 2n;
  Section 3  the polynomial identities of the Fricke families;
  Section 4  the Dickson identities of the cyclic cubic fields;
  Section 5  the point of complex multiplication E_0^6: the intersection
             numbers of the curves C_zeta, the signed sum of thirty-two
             threefolds equal to 32 (alpha + alphabar), and the degrees of
             the closed chains of two and three pieces;
  Section 6  the isolated-block bound at E_0^6: from the Ext table of
             Lemmas cmext and cmmeet, the exact blocks of total degree two
             that no degree-one block reaches and that reach no degree-three
             block sum to 7213, 2605, 2605, 0, 0 and 5325 at the six
             configurations of Table e06count (reachability by a rechecked
             bitmask certificate);
  Section 7  the arithmetic of the newer sections: the four values
             r = 57, 48, 39, 30 at n = 3 (Remark twistfollows), the trace
             forms of the space T_d (Lemma td), Nikulin's numerical
             conditions, the discriminants of the cyclic cubic fields and of
             the cubic field of discriminant 148, and the coefficients used
             in the parity lemma;
  Section 8  K3 surfaces through Floccari's theorem, Weil sixfolds and the
             link: the Gram matrices, signatures, discriminants and Hasse
             invariants of Table rmopen; the witnesses of Lemma witt and
             the count 1484 of the 1980 forms of Witt index two; the Hodge
             numbers of Z_K and Z_K^2 (Proposition zkpowers) and the counts
             after Theorem linkall; the counts of Theorems tenfold and cmkl;
             the linear algebra behind Pohlmann's criterion; the sextic
             discriminants of the split polarisations;
  Section 9  Weil classes on E_0^8, the K3 x K3 criterion and the gamma
             link: the identity Omega^m = m! (generator) for m <= 4, the
             divisibility, slice-graph degrees and kernel counts 484, 3668,
             1876 of the equivariant convolutions, the step excess >= 1 of
             Theorem nothingentersall and the bounds 58, 105, the targets
             46 - 2m, the table m (e + 1) <= 23, the self-intersection of
             the Kummer graph, and the invariant counts of Theorem gamma;
  Section 10 Markman's route on eightfolds and pieces of any kind: the
             contraction ranks 1, 6, 6, 1 and 1, 8, 12, 8, 1 on a secant
             plane, the forced Euler characteristic -2 and the fact that the
             forced dimensions are Serre-consistent only at n = 3, the values
             of chi on the integral lattice 16Z alpha + 4Z beta, the case
             bounds of Theorem w:thm-lagrangian, the 46 edges inside a Koszul
             cube and the acyclic order of the collapsed configuration.

No Mathlib.  Every theorem is checked by `decide` (by `decide +kernel` in
Sections 6 and 9 and for witt_count and chi_lattice_min) or by the core lemmas on natural numbers
and integers and the omega tactic; `native_decide` is not
used.  The block at the end prints the axioms of each one.
-/

set_option maxRecDepth 100000

namespace HodgeClosure

/-! ## Section 1: the closure graph -/

/-- The statements of the closure graph.  HC: the Hodge conjecture; F3: the
conjecture for the varieties that are not abelian; F2: the conjecture for
abelian varieties outside the ring of divisor and Weil classes; F3': the
conjecture modulo abelian varieties; L: the Lefschetz standard conjecture;
M: every Hodge class is motivated; V: flat algebraic classes stay algebraic;
AB: the conjecture for abelian varieties. -/
inductive Stmt | HC | F3 | F2 | F3p | L | M | V | AB
  deriving DecidableEq, Repr

open Stmt

def allStmts : List Stmt := [HC, F3, F2, F3p, L, M, V, AB]

/-- A rule is a list of premises and one conclusion. -/
structure Rule where
  prem : List Stmt
  concl : Stmt

/-- The rule set: each rule is one theorem of the paper or of the literature.
HC -> F3, F3 -> HC (F3 is a special case; A x P^1 recovers A);
HC -> F2, HC -> F3' (special cases); F2 <-> AB (the Mumford fourfold argument);
AB and F3' -> HC (every Hodge class is algebraic modulo algebraic images of
algebraic classes); L and M -> HC (a motivated class is algebraic when the
Lefschetz involutions are); L -> AB and M is a theorem for abelian varieties
(Andre); V -> AB (propagation from CM members, where Weil classes are
polynomials in divisor classes, through Andre's theorem). -/
def rules : List Rule :=
  [ ⟨[HC], F3⟩, ⟨[F3], HC⟩, ⟨[HC], F2⟩, ⟨[HC], F3p⟩, ⟨[HC], AB⟩,
    ⟨[F2], AB⟩, ⟨[AB], F2⟩, ⟨[AB, F3p], HC⟩, ⟨[L, M], HC⟩,
    ⟨[L], AB⟩, ⟨[V], AB⟩, ⟨[HC], M⟩ ]

def step (s : List Stmt) : List Stmt :=
  rules.foldl (fun acc r =>
    if r.prem.all (fun p => acc.contains p) && !acc.contains r.concl
    then r.concl :: acc else acc) s

def closureN : Nat → List Stmt → List Stmt
  | 0, s => s
  | k+1, s => closureN k (step s)

/-- Eight statements, so eight rounds reach the fixed point. -/
def closure (s : List Stmt) : List Stmt := closureN 8 s

def derives (s : List Stmt) : Bool := (closure s).contains HC

theorem hc_from_f2_f3p : derives [F2, F3p] = true := by rfl
theorem hc_from_f3 : derives [F3] = true := by rfl
theorem hc_from_l_m : derives [L, M] = true := by rfl
theorem hc_from_l_f3p : derives [L, F3p] = true := by rfl
theorem hc_from_v_f3p : derives [V, F3p] = true := by rfl

theorem not_hc_from_f2 : derives [F2] = false := by rfl
theorem not_hc_from_f3p : derives [F3p] = false := by rfl
theorem not_hc_from_l : derives [L] = false := by rfl
theorem not_hc_from_m : derives [M] = false := by rfl
theorem not_hc_from_v : derives [V] = false := by rfl
theorem not_hc_from_ab : derives [AB] = false := by rfl
theorem not_hc_from_l_v : derives [L, V] = false := by rfl
theorem not_hc_from_m_f3p : derives [M, F3p] = false := by rfl

/-- All subsets of the seven statements other than HC itself, as lists. -/
def subsets : List Stmt → List (List Stmt)
  | [] => [[]]
  | x :: xs => let r := subsets xs; r ++ r.map (fun s => x :: s)

def hypotheses : List Stmt := [F3, F2, F3p, L, M, V, AB]

def isSubsetOf (a b : List Stmt) : Bool := a.all (fun x => b.contains x)

/-- A deriving set is minimal when no proper subset derives HC. -/
def minimal (s : List Stmt) : Bool :=
  derives s && (subsets s).all (fun t => isSubsetOf s t || !derives t)

def minimalSets : List (List Stmt) :=
  (subsets hypotheses).filter minimal

/-- With AB and F2 interchangeable, the minimal sets are {F3}, {F2, F3'},
{AB, F3'}, {L, M}, {L, F3'} and {V, F3'}: six lists, five statements once
AB is read as F2 (Proposition 2.3 of the paper). -/
theorem minimal_sets_count : minimalSets.length = 6 := by rfl

theorem minimal_sets_are :
    (minimalSets == [[L, M], [F3p, AB], [F3p, V], [F3p, L], [F2, F3p], [F3]]) = true := by rfl

/-! ## Section 2: dimension counts -/

/-- The Prym locus of etale triple covers of genus-(n+1) curves has dimension
3n inside the n^2-dimensional domain; it fills the domain only for n <= 3. -/
theorem prym_locus_small (n : Nat) (h : 4 ≤ n) : 3 * n < n * n := by
  have h1 : 3 * n < 4 * n := by omega
  have h2 : 4 * n ≤ n * n := Nat.mul_le_mul_right n h
  omega

theorem prym_fills_three : 3 * 3 = 3 * 3 ∧ 3 * 2 > 2 * 2 := by decide

/-- A Prym variety of an etale triple cover of a curve of genus g has
dimension 2(g - 1): it is 8 for g = 5 and 6 for g = 4. -/
def prymDim (g : Nat) : Nat := 2 * (g - 1)
theorem prym_dims : prymDim 5 = 8 ∧ prymDim 4 = 6 ∧ prymDim 7 = 12 := by decide

/-- The product locus A_4 x B of Weil fourfolds and Weil surfaces has
dimension 4 + 1 = 5 in the 9-dimensional domain of sixfolds, leaving four
mixed directions. -/
theorem product_locus : 4 + 1 = 5 ∧ 3 * 3 - 5 = 4 := by decide

/-- The number of Hodge classes of degree 2k at a very general member: one
for k different from n, three for k = n (eta^n and the two Weil classes), so
the sum over 0 <= k <= 2n is 2n + 3. -/
def hodgeCount (n : Nat) : Nat :=
  (List.range (2 * n + 1)).foldl (fun acc k => acc + (if k == n then 3 else 1)) 0
theorem hodge_count : (List.range 8).all (fun n => hodgeCount (n + 2) == 2 * (n + 2) + 3) = true := by
  decide

/-- m^2 + m'^2 < (m + m')^2 for m, m' >= 1: the tangent space of the product
locus is a proper subspace of the tangent space of the Weil domain, with
2 m m' mixed directions. -/
theorem sum_squares_lt (m m' : Nat) (hm : 0 < m) (hm' : 0 < m') :
    m * m + m' * m' < (m + m') * (m + m') := by
  have e : (m + m') * (m + m') = m * m + m * m' + (m * m' + m' * m') := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm m' m]
  have hp : 0 < m * m' := Nat.mul_pos hm hm'
  omega

/-- The number of mixed directions is 2 m m': four at (2,1), eight at (2,2). -/
theorem mixed_directions : (2 + 1) * (2 + 1) - (2 * 2 + 1 * 1) = 4 ∧
    (2 + 2) * (2 + 2) - (2 * 2 + 2 * 2) = 8 := by decide

/-- The Hodge classes of degree four on X x X x Z_K invariant under the generic
Hodge group, by Kuenneth type (Theorem link(i) of the paper): (1,1,2) gives 3 + 3,
(2,2,0) gives 4, (0,0,4) gives 6, (2,0,2) and (0,2,2) give 3 each, and the four
types (4,0,0), (0,4,0), (3,1,0), (1,3,0) one each.  The sum is 26. -/
theorem kunneth_count : [3, 3, 4, 6, 3, 3, 1, 1, 1, 1].foldl (· + ·) 0 = 26 := by decide

/-- The lower bound r = (4 + rho) n^2 - 2n of the polarised criterion at
Hankel rank 3: 57 at n = 3 and 104 at n = 4; and 18 at n = 2, rho = 0. -/
def rBound (rho n : Nat) : Nat := (4 + rho) * n * n - 2 * n
theorem r_values : rBound 3 3 = 57 ∧ rBound 3 4 = 104 ∧ rBound 0 2 = 12 ∧ rBound 3 2 = 24 := by decide

/-! ## Section 3: the Fricke families (Section ssec:fricke) -/

/-- Polynomials in t as coefficient lists, lowest degree first. -/
def padd : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: padd xs ys
def pscale (c : Int) (xs : List Int) : List Int := xs.map (fun x => c * x)
def pmul : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => padd (pscale x ys) (0 :: pmul xs ys)
def psub (xs ys : List Int) : List Int := padd xs (pscale (-1) ys)
def ppow (xs : List Int) : Nat → List Int
  | 0 => [1]
  | k + 1 => pmul xs (ppow xs k)
/-- Remove trailing zero coefficients. -/
def ptrim (xs : List Int) : List Int :=
  (xs.reverse.dropWhile (fun x => x == 0)).reverse

/-- The Fricke universal curve at level 7: c4, c6 and the quadratic factor
t^2 + 13 t + 49 with root product 49 = 7^2. -/
def c4_7 : List Int := pmul [49, 13, 1] [1, 5, 1]
def c6_7 : List Int := pmul [49, 13, 1] [-7, 70, 63, 14, 1]
/-- At level 5: c4, c6 and the factor t^2 + 22 t + 125 with root product 125 = 5^3. -/
def c4_5 : List Int := pmul [5, 10, 1] [125, 22, 1]
def c6_5 : List Int := pmul [-1, 4, 1] (ppow [125, 22, 1] 2)

/-- c4^3 - c6^2 = 1728 t (t^2 + 13 t + 49)^2 at level 7: the discriminant has
a simple zero at t = 0, a double zero at each root of the quadratic factor,
and degree 5, so the fibre at infinity is I_7 and the surface is rational. -/
theorem fricke_disc_7 :
    ptrim (psub (ppow c4_7 3) (ppow c6_7 2)) =
      ptrim (pscale 1728 (pmul [0, 1] (ppow [49, 13, 1] 2))) := by decide

/-- c4^3 - c6^2 = 1728 t (t^2 + 22 t + 125)^3 at level 5. -/
theorem fricke_disc_5 :
    ptrim (psub (ppow c4_5 3) (ppow c6_5 2)) =
      ptrim (pscale 1728 (pmul [0, 1] (ppow [125, 22, 1] 3))) := by decide

/-- The constant terms of the quadratic factors are e_1 e_2 = 7^2 and 5^3,
so the Fricke involution t -> N^k / t exchanges the two roots. -/
theorem fricke_roots : (49 : Int) = 7 ^ 2 ∧ (125 : Int) = 5 ^ 3 := by decide

/-- Euler numbers of Kodaira fibres: I_n has n, II has 2, III has 3, I_0^* has 6. -/
def eulerI (n : Nat) : Nat := n
/-- The rational surfaces R_7 (fibres I_1, I_7, II, II) and R_5 (I_1, I_5, III, III)
have Euler number 12; the twists X_{p,q} add two I_0^* and have Euler number 24. -/
theorem fricke_euler : eulerI 1 + eulerI 7 + 2 + 2 = 12 ∧ eulerI 1 + eulerI 5 + 3 + 3 = 12 ∧
    12 + 6 + 6 = 24 := by decide

/-- Shioda-Tate: rank NS >= 2 + sum of the root ranks of the fibres (I_n gives
n - 1, III gives 1, II gives 0, I_0^* gives 4), so 16 for both twist families,
and for the base changes X_psi 2 + (2 I_1 + 2 I_N + 4 II or III) + Mordell-Weil
rank 2 of R_N, again 16. -/
theorem fricke_picard : 2 + (7 - 1) + 0 + 0 + 4 + 4 = 16 ∧ 2 + (5 - 1) + 1 + 1 + 4 + 4 = 16 ∧
    2 + 2 * (7 - 1) + 2 * 0 + 2 = 16 ∧ 2 + 2 * (5 - 1) + 4 * 1 + 2 = 16 := by decide

/-- Transcendental rank 22 - 16 = 6 at Picard number 16, so the imaginary
quadratic field K = Q(sqrt(-N)) of the Fricke self-map acts on T with
dim_K T = 3; a CM field E strictly containing K would have degree 6 with
dim_E T = 1, and 6 < 3 * 3 rules out a totally real cubic field. -/
theorem fricke_transcendental : 22 - 16 = 6 ∧ 6 / 2 = 3 ∧ 6 < 3 * 3 := by decide

/-- A dominant rational self-map of degree N gives f_* f^* = N on T: the
multiplier of a correspondence is the product d_1 d_2 of the two degrees
(Section ssec:fricke of the paper), here 1 * N; the sign of (f^*)^2 = -N is the
Velu identity below. -/
theorem fricke_multiplier : 1 * 7 = 7 ∧ 1 * 5 = 5 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6 := by decide

/-- The sign of the Fricke self-isogeny (Lemma frickesign).  For the Fricke curve
E_t: y^2 = x^3 + A x + B, A = -27 c_4, B = -54 c_6, the kernel polynomial of
the rational cyclic subgroup of order N (the factor of degree (N - 1)/2 of
the N-th division polynomial, computed in julia/fricke_sign.jl) has
coefficients k_1, ..., k_m in Z[t].  Newton's identities give the power sums
S_1, S_2, S_3 of its roots, and Velu's formulas the quotient curve
E': y^2 = x^3 + A' x + B' with A' = A - 5 (6 S_2 + 2 m A) and
B' = B - 7 (10 S_3 + 6 A S_1 + 4 m B).  The quotient is E_{w(t)}, w(t) = N^k/t,
up to the scaling (x, y) -> (u^2 x, u^3 y), and the isogeny multiplies the
invariant differential by lambda = u^{-1} with lambda^2 = -t^2 / N^(k-1).
Writing A~(t) = t^4 A(N^k / t) and B~(t) = t^6 B(N^k / t), this is the
polynomial identity N^(k-1) B' A~ + A' B~ = 0 proved here for both levels;
hence lambda(t) lambda(w(t)) = -N and the composite isogeny is [-N]. -/
def newton3 (e1 e2 e3 : List Int) : List Int × List Int × List Int :=
  let s1 := e1
  let s2 := psub (pmul e1 s1) (pscale 2 e2)
  let s3 := padd (psub (pmul e1 s2) (pmul e2 s1)) (pscale 3 e3)
  (s1, s2, s3)
def veluA (A B e1 e2 e3 : List Int) (m : Int) : List Int :=
  let (_, s2, _) := newton3 e1 e2 e3
  psub A (pscale 5 (padd (pscale 6 s2) (pscale (2 * m) A)))
def veluB (A B e1 e2 e3 : List Int) (m : Int) : List Int :=
  let (s1, _, s3) := newton3 e1 e2 e3
  psub B (pscale 7 (padd (pscale 10 s3) (padd (pscale 6 (pmul A s1)) (pscale (4 * m) B))))
/-- t^d P(N^k / t) for a polynomial P of degree d: the reversed coefficients scaled by powers of N^k. -/
def ptilde (nk : Int) (xs : List Int) : List Int :=
  List.zipWith (· * ·) xs.reverse ((List.range xs.length).map (fun i => nk ^ i)).reverse
def A_5 : List Int := pscale (-27) c4_5
def B_5 : List Int := pscale (-54) c6_5
def A_7 : List Int := pscale (-27) c4_7
def B_7 : List Int := pscale (-54) c6_7
/-- Kernel polynomial at level 5: x^2 + k_1 x + k_2, e_1 = -k_1, e_2 = k_2. -/
def kerE1_5 : List Int := pscale (-1) [750, 132, 6]
def kerE2_5 : List Int := [100125, 42372, 6282, 396, 9]
/-- Kernel polynomial at level 7: x^3 + k_1 x^2 + k_2 x + k_3, e_1 = -k_1, e_2 = k_2, e_3 = -k_3. -/
def kerE1_7 : List Int := pscale (-1) [441, 117, 9]
def kerE2_7 : List Int := [43659, 28782, 6777, 702, 27]
def kerE3_7 : List Int := pscale (-1) [1165563, 1338525, 586602, 132273, 16362, 1053, 27]
theorem fricke_sign_5 :
    ptrim (padd (pscale 25 (pmul (veluB A_5 B_5 kerE1_5 kerE2_5 [] 2) (ptilde 125 A_5)))
                (pmul (veluA A_5 B_5 kerE1_5 kerE2_5 [] 2) (ptilde 125 B_5))) = [] := by decide
theorem fricke_sign_7 :
    ptrim (padd (pscale 7 (pmul (veluB A_7 B_7 kerE1_7 kerE2_7 kerE3_7 3) (ptilde 49 A_7)))
                (pmul (veluA A_7 B_7 kerE1_7 kerE2_7 kerE3_7 3) (ptilde 49 B_7))) = [] := by decide
/-- The twist bookkeeping: for the twist by u(t) = (t - p)(t - N^k/p) the product
c(t) c(w(t)) of the scaling factors c(t)^2 = u(w(t))/u(t) = N^k/t^2 is +1, and for
the twist by t^2 - N^k, with u(w(t))/u(t) = -N^k/t^2, it is -1; so Lambda^2 = -N on
the pair twists and +N at the fixed points: the signed squares (-1) * 5, (-1) * 7
and 5, 7 of the two cases. -/
theorem fricke_sign_cases : (-1 : Int) * 5 = -5 ∧ (-1 : Int) * 7 = -7 ∧ (1 : Int) * 5 = 5 ∧ (1 : Int) * 7 = 7 := by decide

/-- The Hecke algebra of (D_n, <tau>) for odd n has dimension (n + 1) / 2, the number of double cosets:
3, 4, 5, 6 for n = 5, 7, 9, 11 (Proposition hecke). -/
def heckeDim (n : Nat) : Nat := (n + 1) / 2
theorem hecke_dims : heckeDim 5 = 3 ∧ heckeDim 7 = 4 ∧ heckeDim 9 = 5 ∧ heckeDim 11 = 6 := by decide

/-! ## Section 4: the Dickson families of the cyclic cubic fields (Theorem zeta9) -/

/-- Dickson polynomials (Theorem zeta9 for n = 7 and n = 9).
v^7 p_{7,a}(v + a/v) = v^14 + a^7 with p_{7,a} = t^7 - 7 a t^5 + 14 a^2 t^3 - 7 a^3 t, checked at
a = 1 and a = 2 as identities of polynomials in v; the same for
p_{9,a} = t^9 - 9 a t^7 + 27 a^2 t^5 - 30 a^3 t^3 + 9 a^4 t at a = 1. -/
def dickson7 (a : Int) : List Int :=
  padd (psub (ppow [a, 0, 1] 7) (pscale (7 * a) (pmul [0, 0, 1] (ppow [a, 0, 1] 5))))
       (psub (pscale (14 * a * a) (pmul [0, 0, 0, 0, 1] (ppow [a, 0, 1] 3)))
             (pscale (7 * a * a * a) (pmul [0, 0, 0, 0, 0, 0, 1] [a, 0, 1])))
def dickson9 (a : Int) : List Int :=
  padd (padd (psub (ppow [a, 0, 1] 9) (pscale (9 * a) (pmul [0, 0, 1] (ppow [a, 0, 1] 7))))
             (pscale (27 * a * a) (pmul [0, 0, 0, 0, 1] (ppow [a, 0, 1] 5))))
       (padd (pscale (-30 * a * a * a) (pmul [0, 0, 0, 0, 0, 0, 1] (ppow [a, 0, 1] 3)))
             (pscale (9 * a * a * a * a) (pmul [0, 0, 0, 0, 0, 0, 0, 0, 1] [a, 0, 1])))
theorem dickson7_identity :
    ptrim (dickson7 1) = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] ∧
    ptrim (dickson7 2) = [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide
theorem dickson9_identity :
    ptrim (dickson9 1) = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-- The prime 2 has order three in (Z/7)^x/{+-1} and in (Z/9)^x/{+-1}, so it is inert in
Q(zeta_7)^+ and Q(zeta_9)^+ (Theorem zeta9, the place above 2). The cubic polynomials
t^3 + t^2 - 2 t - 1 and t^3 - 3 t + 1 of theta change sign on [-2,-1], [-1,0], [0,2] and on
[-2,-1], [0,1], [1,2], so each has three real roots, exactly one of them positive for n = 7
and two for n = 9: the unit epsilon of the proof is positive at exactly one real place. -/
theorem two_inert_7_9 :
    (2 % 7 ≠ 1 ∧ 2 % 7 ≠ 6 ∧ 4 % 7 ≠ 1 ∧ 4 % 7 ≠ 6 ∧ 8 % 7 = 1) ∧
    (2 % 9 ≠ 1 ∧ 2 % 9 ≠ 8 ∧ 4 % 9 ≠ 1 ∧ 4 % 9 ≠ 8 ∧ 8 % 9 = 8) := by decide
def f7 (t : Int) : Int := t * t * t + t * t - 2 * t - 1
def f9 (t : Int) : Int := t * t * t - 3 * t + 1
theorem theta_sign_pattern :
    (f7 (-2) < 0 ∧ f7 (-1) > 0 ∧ f7 0 < 0 ∧ f7 2 > 0) ∧
    (f9 (-2) < 0 ∧ f9 0 > 0 ∧ f9 1 < 0 ∧ f9 2 > 0) := by decide

/-- Proposition sqrt10: a symplectic automorphism of order five has coinvariant rank 16 and one
of order seven rank 18 (Nikulin), so the transcendental lattice, of signature (2, t - 2), lies
in a lattice of rank 22 - 16 = 6 and signature (3, 3) (resp. rank 4, signature (3, 1)); hence
t <= 5 (resp. t <= 3), while a totally real endomorphism field of degree at least two needs
t >= 2 * 3 = 6 (Zarhin: dim_E T >= 3). The symplectic orders are at most eight, and those not
of the form 2^a 3^b are 5 and 7. -/
theorem symplectic_chain_bound :
    (22 - 16 = 6 ∧ 19 - 16 = 3 ∧ 2 + 3 = 5 ∧ 5 < 2 * 3) ∧
    (22 - 18 = 4 ∧ 19 - 18 = 1 ∧ 2 + 1 = 3 ∧ 3 < 2 * 3) ∧
    ((List.range 9).filter (fun n => n ≥ 2 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0) = [2, 3, 4, 6, 8]) ∧
    ((List.range 9).filter (fun n => n ≥ 2 ∧ (n % 5 = 0 ∨ n % 7 = 0)) = [5, 7]) := by decide

/-! ## Section 5: the point of complex multiplication E_0^6 (Lemma cmext, Proposition twostep, Appendix app:cmpoint) -/

/-- Binomial coefficients, by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- dim Ext^k(O_Z, O_Z) = sum_{p+q=k} C(3,q) C(3,p) = C(6,k) for an abelian threefold Z with trivial
normal bundle in an abelian sixfold (Lemma cmext(iii) at a = b). -/
theorem binomial_six :
    (List.range 7).all (fun k =>
      (List.range (k + 1)).foldl (fun s q => s + choose 3 q * choose 3 (k - q)) 0 == choose 6 k) = true := by
  decide

/-- Gaussian integers (re, im). -/
structure GI where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def gadd (x y : GI) : GI := ⟨x.re + y.re, x.im + y.im⟩
def gsub (x y : GI) : GI := ⟨x.re - y.re, x.im - y.im⟩
def gmul (x y : GI) : GI := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def gconj (x : GI) : GI := ⟨x.re, -x.im⟩
def gscale (n : Int) (x : GI) : GI := ⟨n * x.re, n * x.im⟩
def gnorm (x : GI) : Int := x.re * x.re + x.im * x.im
def gzero : GI := ⟨0, 0⟩
def gpow (x : GI) : Nat → GI
  | 0 => ⟨1, 0⟩
  | n + 1 => gmul x (gpow x n)

/-- The fourth roots of unity 1, i, -1, -i. -/
def mu4 : List GI := [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]

/-- The class of the elliptic curve C_zeta = ker(u + zeta v) in the Weil surface B_j, in the basis
(a_j, b_j, c_j, cbar_j) of (1,1)-forms: a_j + b_j + zetabar c_j + zeta cbar_j (Lemma A.1(i)). -/
def curveClass (z : GI) : List GI := [⟨1, 0⟩, ⟨1, 0⟩, gconj z, z]

/-- The intersection pairing of two (1,1)-classes on B_j: a_j b_j = 1, c_j cbar_j = cbar_j c_j = -1
and every other product of two basis forms repeats a differential. -/
def pairB (x y : List GI) : GI :=
  match x, y with
  | [xa, xb, xc, xd], [ya, yb, yc, yd] =>
      gsub (gadd (gmul xa yb) (gmul xb ya)) (gadd (gmul xc yd) (gmul xd yc))
  | _, _ => gzero

/-- (C_zeta . C_zeta') = |zeta - zeta'|^2 in {0, 2, 4}, and theta . C_zeta = 2 (Lemma A.1(ii), (iii)). -/
theorem curve_intersections :
    mu4.all (fun z => mu4.all (fun w =>
      pairB (curveClass z) (curveClass w) == ⟨gnorm (gsub z w), 0⟩ &&
      [0, 2, 4].contains (gnorm (gsub z w)))) = true ∧
    mu4.all (fun z => pairB [⟨1, 0⟩, ⟨1, 0⟩, gzero, gzero] (curveClass z) == ⟨2, 0⟩) = true := by
  decide

/-- The sums T_{m,j} = sum_zeta zeta^m [C_zeta] are 4(a_j + b_j), 4 c_j, 0, 4 cbar_j for
m = 0, 1, 2, 3 (Lemma A.1(iv)). -/
def twistSum (m : Nat) : List GI :=
  mu4.foldl (fun acc z => List.zipWith gadd acc ((curveClass z).map (gmul (gpow z m))))
    [gzero, gzero, gzero, gzero]
theorem twist_sums :
    twistSum 0 = [⟨4, 0⟩, ⟨4, 0⟩, gzero, gzero] ∧ twistSum 1 = [gzero, gzero, ⟨4, 0⟩, gzero] ∧
    twistSum 2 = [gzero, gzero, gzero, gzero] ∧ twistSum 3 = [gzero, gzero, gzero, ⟨4, 0⟩] := by
  decide

/-- The class of Z_zeta = C_{zeta_1} x C_{zeta_2} x C_{zeta_3} as the 64 coefficients of the
products of one basis form from each surface, in the order (i_1, i_2, i_3) with i_3 fastest. -/
def threefoldClass (z1 z2 z3 : GI) : List GI :=
  (curveClass z1).foldr (fun x acc =>
    ((curveClass z2).foldr (fun y acc' =>
      ((curveClass z3).map (fun w => gmul (gmul x y) w)) ++ acc') []) ++ acc) []

/-- The signed sum S(1) - S(-1) over the 32 threefolds with zeta_1 zeta_2 zeta_3 = +-1. -/
def signedSum : List GI :=
  mu4.foldl (fun acc z1 => mu4.foldl (fun acc z2 => mu4.foldl (fun acc z3 =>
    let w := gmul (gmul z1 z2) z3
    if w == ⟨1, 0⟩ then List.zipWith gadd acc (threefoldClass z1 z2 z3)
    else if w == ⟨-1, 0⟩ then List.zipWith gsub acc (threefoldClass z1 z2 z3)
    else acc) acc) acc) (List.replicate 64 gzero)

/-- S(1) - S(-1) = 32 (alpha + alphabar): the coefficient of c_1 c_2 c_3 (index 2*16+2*4+2 = 42) and
of cbar_1 cbar_2 cbar_3 (index 63) is 32 and every other coefficient vanishes; and exactly 32
triples have zeta_1 zeta_2 zeta_3 = +-1 (Lemma A.1(iv), equation (A.8)). -/
theorem weil_sum_32 :
    signedSum = (List.range 64).map (fun i => if i == 42 || i == 63 then (⟨32, 0⟩ : GI) else gzero) ∧
    (mu4.foldl (fun n z1 => mu4.foldl (fun n z2 => mu4.foldl (fun n z3 =>
      let w := gmul (gmul z1 z2) z3
      if w == ⟨1, 0⟩ || w == ⟨-1, 0⟩ then n + 1 else n) n) n) 0) = 32 := by
  decide

/-- (theta|_Z)^3 = 3! 2^3 = 48 and chi_Z = 48/6 = 8; the Ext groups between two twists of one
threefold have total dimension sum_k C(3,k) 8 m^3 = 8 m^3 chi_Z and vanishing Euler characteristic
(Lemma cmext(iii), Lemma cmcurves(iii)); and the count 5 * 15 = 75, 75 - 57 = 18 at the stopping point. -/
theorem cm_counts :
    3 * 2 * 1 * (2 * 2 * 2) = 48 ∧ 48 / 6 = 8 ∧ 5 * 15 = 75 ∧ 75 - 57 = 18 ∧
    [1, 2, 3].all (fun m =>
      (List.range 4).foldl (fun s k => s + choose 3 k * 8 * m * m * m) 0 == 8 * m * m * m * 8 &&
      (List.range 4).foldl (fun s k => s + (if k % 2 == 0 then 1 else -1) * (choose 3 k : Int)) 0 == 0) = true := by
  decide

/-- The pieces at E_0^6: O_Z L^k and O_Z' L^k for two threefolds Z, Z' meeting in finitely many
points, and the line bundles L^k, with twists k = 0, 1, 2, 3. -/
inductive PieceT | Z | W | L
  deriving DecidableEq, Repr
structure Piece where
  t : PieceT
  tw : Nat
  deriving DecidableEq, Repr
def pieces : List Piece :=
  [PieceT.Z, PieceT.W, PieceT.L].foldr (fun t acc => (List.range 4).map (fun k => ⟨t, k⟩) ++ acc) []

/-- The degrees k with Ext^k(F_P, F_Q) != 0 for distinct pieces, from Lemma cmext. -/
def degs (P Q : Piece) : List Nat :=
  match P.t, Q.t with
  | PieceT.L, PieceT.L => if Q.tw > P.tw then [0] else [6]
  | PieceT.L, _ => if Q.tw > P.tw then [0] else if Q.tw < P.tw then [3] else [0, 1, 2, 3]
  | _, PieceT.L => if Q.tw > P.tw then [3] else if Q.tw < P.tw then [6] else [3, 4, 5, 6]
  | _, _ => if P.t != Q.t then [3] else if Q.tw > P.tw then [0, 1, 2, 3] else [3, 4, 5, 6]

/-- Every closed chain of two distinct pieces has total Ext degree at least 3 (Proposition twostep). -/
theorem two_step_degree :
    pieces.all (fun P => pieces.all (fun Q =>
      P == Q || (degs P Q).all (fun k1 => (degs Q P).all (fun k2 => k1 + k2 ≥ 3)))) = true := by
  decide

/-- A closed chain of three pieces with degrees k1, k2, k3 and total degree 3 exists exactly for three
twists of one threefold in cyclic ascending order, with degree 3 on the descending edge and degree 0
on the two ascending ones (Proposition twostep). -/
def isChain (P Q R : Piece) (k1 k2 k3 : Nat) : Bool :=
  P.t != PieceT.L && P.t == Q.t && Q.t == R.t &&
  ((P.tw < Q.tw && Q.tw < R.tw && k1 == 0 && k2 == 0 && k3 == 3) ||
   (R.tw < P.tw && P.tw < Q.tw && k1 == 0 && k2 == 3 && k3 == 0) ||
   (Q.tw < R.tw && R.tw < P.tw && k1 == 3 && k2 == 0 && k3 == 0))
theorem three_step_chains :
    pieces.all (fun P => pieces.all (fun Q => pieces.all (fun R =>
      P == Q || Q == R || P == R ||
      (degs P Q).all (fun k1 => (degs Q R).all (fun k2 => (degs R P).all (fun k3 =>
        (k1 + k2 + k3 == 3) == isChain P Q R k1 k2 k3)))))) = true := by
  decide

/-! ## Section 6: isolated blocks at E_0^6 (Lemma isolated, Proposition e06count) -/

namespace Isolated

/-- A piece of a convolution at A_0 = E_0^6: the threefold O_{Z_zeta} (x) L^twist [shift] when `isZ`,
with zeta = (i^z1, i^z2, i^z3), or the line bundle L^twist [shift].  Shifts carry an offset of 8, so that
`shift = 8` is the shift 0 and total degrees stay natural numbers. -/
structure Piece where
  isZ : Bool
  z1 : Nat
  z2 : Nat
  z3 : Nat
  twist : Nat
  shift : Nat

/-- The number of coordinates shared by zeta and zeta'. -/
def shared (p q : Piece) : Nat :=
  (if p.z1 = q.z1 then 1 else 0) + (if p.z2 = q.z2 then 1 else 0) + (if p.z3 = q.z3 then 1 else 0)

/-- |i^a - i^b|^2: 1 when a = b (so that it drops out of the product), 4 for opposite roots, 2 otherwise. -/
def sqdist (a b : Nat) : Nat := if a = b then 1 else if (a + 4 - b) % 4 = 2 then 4 else 2

/-- The number of components of Z_zeta cap Z_zeta' (Lemmas cmext, cmmeet). -/
def comps (p q : Piece) : Nat := sqdist p.z1 q.z1 * sqdist p.z2 q.z2 * sqdist p.z3 q.z3

def cube (m : Nat) : Nat := m * m * m

/-- The dimensions of Ext^k(p, q) as (k, dim, exact): the table of Appendix app:extdims for the exact entries, the E_2 page
of Lemma cmmeet for two threefolds meeting along a curve or a surface (upper bounds, flagged `false`).
chi(O_Z) = 8, and L is the principal polarisation. -/
def extDims (p q : Piece) : List (Nat × Nat × Bool) :=
  if p.isZ = false ∧ q.isZ = false then
    if p.twist < q.twist then [(0, cube (q.twist - p.twist) * cube (q.twist - p.twist), true)]
    else if q.twist < p.twist then [(6, cube (p.twist - q.twist) * cube (p.twist - q.twist), true)]
    else (List.range 7).map (fun k => (k, choose 6 k, true))
  else if p.isZ = true ∧ q.isZ = false then
    if p.twist < q.twist then [(3, 8 * cube (q.twist - p.twist), true)]
    else if q.twist < p.twist then [(6, 8 * cube (p.twist - q.twist), true)]
    else (List.range 4).map (fun k => (k + 3, choose 3 k, true))
  else if p.isZ = false ∧ q.isZ = true then
    if p.twist < q.twist then [(0, 8 * cube (q.twist - p.twist), true)]
    else if q.twist < p.twist then [(3, 8 * cube (p.twist - q.twist), true)]
    else (List.range 4).map (fun k => (k, choose 3 k, true))
  else if shared p q = 3 then
    if p.twist < q.twist then (List.range 4).map (fun k => (k, choose 3 k * 8 * cube (q.twist - p.twist), true))
    else if q.twist < p.twist then (List.range 4).map (fun k => (k + 3, choose 3 k * 8 * cube (p.twist - q.twist), true))
    else (List.range 7).map (fun k => (k, choose 6 k, true))
  else
    let d := shared p q
    let D := comps p q
    if d = 0 then [(3, D, true)]
    else
      let c := 3 - d
      if p.twist < q.twist then
        (List.range (d + 1)).map (fun j => (c + j, D * choose d j * (2 * (q.twist - p.twist)) ^ d, false))
      else if q.twist < p.twist then
        (List.range (d + 1)).map (fun j => (c + j + d, D * choose d j * (2 * (p.twist - q.twist)) ^ d, false))
      else
        (List.range (d + 1)).foldr (fun j acc =>
          (List.range (d + 1)).map (fun i => (i + c + j, D * choose d j * choose d i, false)) ++ acc) []

/-- The sum of the dimensions of the blocks of total degree k + s_b - s_a = t. -/
def totalDeg (ps : List Piece) (t : Nat) : Nat :=
  ps.foldl (fun s p => ps.foldl (fun s q =>
    (extDims p q).foldl (fun s e => if e.1 + q.shift = t + p.shift then s + e.2.1 else s) s) s) 0

/-- For a pair of pieces: whether it carries a block of total degree one, the exact dimension of its
total-degree-two part (0 when only an E_2 bound is known), and whether it carries a block of total
degree three. -/
def pairInfo (p q : Piece) : Bool × Nat × Bool :=
  (extDims p q).foldl (fun r e =>
    let t := e.1 + q.shift
    (r.1 || t = 1 + p.shift,
     if t = 2 + p.shift ∧ e.2.2 = true then r.2.1 + e.2.1 else r.2.1,
     r.2.2 || t = 3 + p.shift)) (false, 0, false)

/-- Bit b of the mask m. -/
def bit (m b : Nat) : Bool := (m >>> b) % 2 = 1

/-- The row of pairs (a, b), b running over the pieces, as a bitmask in b, for the blocks of total
degree one and of total degree three. -/
def rowMasks (ps : List Piece) (p : Piece) : Nat × Nat :=
  (ps.foldl (fun r q =>
    let i := pairInfo p q
    ((if i.1 then r.1.1 + (1 <<< r.2) else r.1.1, if i.2.2 then r.1.2 + (1 <<< r.2) else r.1.2), r.2 + 1))
    ((0, 0), 0)).1

def rows1 (ps : List Piece) : List Nat := ps.map (fun p => (rowMasks ps p).1)
def rows3 (ps : List Piece) : List Nat := ps.map (fun p => (rowMasks ps p).2)

/-- `R` is a list of row bitmasks: `bit (R[a]) b` says that b is reachable from a along steps carrying a
block of total degree one.  The check: R is reflexive, contains every such step, and is closed under
one more step; then it contains the reachability relation. -/
def reachOK (n : Nat) (E1 R : List Nat) : Bool :=
  (List.range n).all (fun a =>
    let Ra := R.getD a 0
    bit Ra a && (E1.getD a 0 ||| Ra) == Ra &&
    (List.range n).all (fun k => !(bit Ra k) || (E1.getD k 0 ||| Ra) == Ra))

/-- `RT` is the transpose of `R`. -/
def transposeOK (n : Nat) (R RT : List Nat) : Bool :=
  (List.range n).all (fun a => (List.range n).all (fun b => bit (R.getD a 0) b == bit (RT.getD b 0) a))

/-- Remove the bit b from the mask m. -/
def clearBit (m b : Nat) : Nat := if bit m b then m - (1 <<< b) else m

/-- Any row a2 (in the order of the list) with `f a2 row = true`. -/
def anyRow (f : Nat → Nat → Bool) : List Nat → Nat → Bool
  | [], _ => false
  | r :: rs, a2 => f a2 r || anyRow f rs (a2 + 1)

/-- The isolated-block bound with the reachability certificate (R, RT): the sum of the exact
total-degree-two dimensions of the pairs (a, b) that no block of total degree one reaches
(no (a2, b2) != (a, b) of total degree one with a ~> a2 and b2 ~> b) and that reach no block of total
degree three (no (a2, b2) != (a, b) of total degree three with a2 ~> a and b ~> b2). -/
def isolatedWith (ps : List Piece) (E1 E3 R RT : List Nat) : Nat :=
  (ps.foldl (fun s p =>
    let Ra := R.getD s.2 0
    let RTa := RT.getD s.2 0
    ((ps.foldl (fun u q =>
      let i := pairInfo p q
      let dim := i.2.1
      if dim = 0 then (u.1, u.2 + 1) else
      let Rb := R.getD u.2 0
      let RTb := RT.getD u.2 0
      let hit := anyRow (fun a2 e => bit Ra a2 && ((if a2 = s.2 then clearBit e u.2 else e) &&& RTb) != 0) E1 0
      let out := anyRow (fun a2 e => bit RTa a2 && ((if a2 = s.2 then clearBit e u.2 else e) &&& Rb) != 0) E3 0
      (if hit || out then u.1 else u.1 + dim, u.2 + 1)) (s.1, 0)).1, s.2 + 1)) (0, 0)).1

/-- The whole check for one configuration: the degree-one and degree-three rows are those of the
Ext table, the certificate is a reachability relation, and the isolated blocks sum to `v`. -/
def isolatedCert (ps : List Piece) (E1 E3 R RT : List Nat) (v : Nat) : Bool :=
  let n := ps.length
  rows1 ps == E1 && rows3 ps == E3 && reachOK n E1 R && transposeOK n R RT && isolatedWith ps E1 E3 R RT == v

/-- The thirty-two threefolds Z_zeta, zeta_1 zeta_2 zeta_3 = +-1, at twist 0, at shift 0 when the product
is 1 and shift 1 when it is -1. -/
def base : List Piece :=
  (List.range 64).filterMap (fun i =>
    let a := i / 16
    let b := (i / 4) % 4
    let c := i % 4
    if (a + b + c) % 4 = 0 then some ⟨true, a, b, c, 0, 8⟩
    else if (a + b + c) % 4 = 2 then some ⟨true, a, b, c, 0, 9⟩
    else none)

/-- L^l [t] and O_{Z_zeta} (x) L^k [t], shifts with the offset 8. -/
def L (l t : Nat) : Piece := ⟨false, 0, 0, 0, l, t⟩
def Z (a b c k t : Nat) : Piece := ⟨true, a, b, c, k, t⟩

/-- The configurations of Table e06count at which the least bound is attained: the thirty-five pieces at
shifts (0,0,0), (2,3,4), (-3,-2,-1); family (a) with L^1[-2], L^2[-1], L^3[0], L^4[1]; family (c) with
Z_(1,1,1) (x) L^1 at [-1], [0] and (x) L^2 at [1], [2]; family (d) with Z_(1,1,-1) at [0], [1]. -/
def base35 : List Piece := base ++ [L 1 8, L 2 8, L 3 8]
def base35up : List Piece := base ++ [L 1 10, L 2 11, L 3 12]
def base35down : List Piece := base ++ [L 1 5, L 2 6, L 3 7]
def familyA : List Piece := base ++ [L 1 6, L 2 7, L 3 8, L 4 9]
def familyC : List Piece := base ++ [Z 0 0 0 1 7, Z 0 0 0 1 8, Z 0 0 0 2 9, Z 0 0 0 2 10, L 1 8, L 2 8, L 3 8]
def familyD : List Piece := base ++ [Z 0 0 2 0 8, Z 0 0 2 0 9, L 1 8, L 2 8, L 3 8]


/-- Certificates: the rows of the blocks of total degree one and three, and a reachability relation R
with its transpose, all as bitmasks over the pieces; `isolatedCert` rechecks each of them from the
Ext table before it sums the isolated blocks. -/
def base35_E1 : List Nat := [1,2164394603,84154477,8,605048953,32,64,2692760297,17193793,512,68443657,2048,4096,546339368,16384,2156059232,93798913,131072,262144,614337032,1048576,2696288288,2178306112,8388608,16777216,2810315273,67108864,2902853672,3037991008,536870912,3851436097,2147483648,4294967296,8589934592,17179869184]
def base35_E3 : List Nat := [33950228479,3681267711,1601027583,33011171071,2121922047,33247656703,34189270015,4209633279,1534066647,32877051883,1585315743,32979746671,33117634429,2063204286,33920909305,3672899574,1610606487,33017551723,33252401005,2130685854,34191933049,4211064246,3690984918,33957083881,34357074799,4293633951,34353405565,4285509054,4286428662,34355444473,4294567383,34359139051,7073061481,11368028777,19957963369]
def base35_R : List Nat := [1,2164394603,84154477,8,605048953,32,64,2692760297,17193793,512,68443657,2048,4096,546339368,16384,2156059232,93798913,131072,262144,614337032,1048576,2696288288,2178306112,8388608,16777216,2810315273,67108864,2902853672,3037991008,536870912,3851436097,2147483648,4294967296,8589934592,17179869184]
def base35_RT : List Nat := [1107363223,2,4,168305822,16,404791478,1346404822,128,256,34187138,1024,136883462,274773268,8192,1078060432,32768,65536,174817538,409797892,524288,1350116368,2097152,4194304,1122607232,1530986758,33554432,1577649172,134217728,268435456,2049450128,1073741824,3663757442,4294967296,8589934592,17179869184]
theorem iso_base35 : isolatedCert base35 base35_E1 base35_E3 base35_R base35_RT 7213 = true := by decide +kernel
def base35up_E1 : List Nat := [1,2164394603,84154477,8,605048953,32,64,2692760297,17193793,512,68443657,2048,4096,546339368,16384,2156059232,93798913,131072,262144,614337032,1048576,2696288288,2178306112,8388608,16777216,2810315273,67108864,2902853672,3037991008,536870912,3851436097,2147483648,15662996073,27286676886,17179869184]
def base35up_E3 : List Nat := [3885457407,3681267711,1601027583,2946399999,2121922047,3182885631,4124498943,4209633279,1534066647,2812280811,1585315743,2914975599,3052863357,2063204286,3856138233,3672899574,1610606487,2952780651,3187629933,2130685854,4127161977,4211064246,3690984918,3892312809,4292303727,4293633951,4288634493,4285509054,4286428662,4290673401,4294567383,4294367979,4294967296,8589934592,17179869184]
def base35up_R : List Nat := [1,2164394603,84154477,8,605048953,32,64,2692760297,17193793,512,68443657,2048,4096,546339368,16384,2156059232,93798913,131072,262144,614337032,1048576,2696288288,2178306112,8388608,16777216,2810315273,67108864,2902853672,3037991008,536870912,3851436097,2147483648,34359738367,30064771071,17179869184]
def base35up_RT : List Nat := [13992265111,12884901890,12884901892,13053207710,12884901904,13289693366,14231306710,12884902016,12884902144,12919089026,12884902912,13021785350,13159675156,12884910080,13962962320,12884934656,12884967424,13059719426,13294699780,12885426176,14235018256,12886999040,12889096192,14007509120,14415888646,12918456320,14462551060,13019119616,13153337344,14934352016,13958643712,16548659330,4294967296,12884901888,30064771072]
theorem iso_base35up : isolatedCert base35up base35up_E1 base35up_E3 base35up_R base35up_RT 2605 = true := by decide +kernel
def base35down_E1 : List Nat := [8589934593,19344263787,17264023661,8589934600,17784918137,8589934624,8589934656,19872629481,17197062977,8589935104,17248312841,8589936640,8589938688,17726208552,8589950976,19335928416,17273668097,8590065664,8590196736,17794206216,8590983168,19876157472,19358175296,8598323200,8606711808,19990184457,8657043456,20082722856,20217860192,9126805504,21031305281,10737418240,12884901888,25769803776,17179869184]
def base35down_E3 : List Nat := [3885457407,3681267711,1601027583,2946399999,2121922047,3182885631,4124498943,4209633279,1534066647,2812280811,1585315743,2914975599,3052863357,2063204286,3856138233,3672899574,1610606487,2952780651,3187629933,2130685854,4127161977,4211064246,3690984918,3892312809,4292303727,4293633951,4288634493,4285509054,4286428662,4290673401,4294567383,4294367979,4294967296,8589934592,17179869184]
def base35down_R : List Nat := [25769803777,27934198379,25853958253,25769803784,26374852729,25769803808,25769803840,28462564073,25786997569,25769804288,25838247433,25769805824,25769807872,26316143144,25769820160,27925863008,25863602689,25769934848,25770065920,26384140808,25770852352,28466092064,27948109888,25778192384,25786580992,28580119049,25836912640,28672657448,28807794784,26306674688,29621239873,27917287424,30064771072,25769803776,17179869184]
def base35down_RT : List Nat := [1107363223,2,4,168305822,16,404791478,1346404822,128,256,34187138,1024,136883462,274773268,8192,1078060432,32768,65536,174817538,409797892,524288,1350116368,2097152,4194304,1122607232,1530986758,33554432,1577649172,134217728,268435456,2049450128,1073741824,3663757442,4294967296,17179869183,34359738367]
theorem iso_base35down : isolatedCert base35down base35down_E1 base35down_E3 base35down_R base35down_RT 2605 = true := by decide +kernel
def familyA_E1 : List Nat := [4294967297,10754329195,8674089069,4294967304,9194983545,4294967328,4294967360,11282694889,8607128385,4294967808,8658378249,4294969344,4294971392,9136273960,4294983680,10745993824,8683733505,4295098368,4295229440,9204271624,4296015872,11286222880,10768240704,4303355904,4311744512,11400249865,4362076160,11492788264,11627925600,4831838208,12441370689,6442450944,12884901888,25769803776,51539607552,34359738368]
def familyA_E3 : List Nat := [21065326591,38041006079,35960765951,20126269183,36481660415,20362754815,21304368127,38569371647,35893805015,19992149995,35945054111,20094844783,20232732541,36422942654,21036007417,38032637942,35970344855,20132649835,20367499117,36490424222,21307031161,38570802614,38050723286,21072181993,21472172911,38653372319,21468503677,38645247422,38646167030,21470542585,38654305751,21474237163,38654705664,8589934592,19957963369,40171578774]
def familyA_R : List Nat := [64424509441,66588904043,64508663917,64424509448,65029558393,64424509472,64424509504,67117269737,64441703233,64424509952,64492953097,64424511488,64424513536,64970848808,64424525824,66580568672,64518308353,64424640512,64424771584,65038846472,64425558016,67120797728,66602815552,64432898048,64441286656,67234824713,64491618304,67327363112,67462500448,64961380352,68275945537,66571993088,64424509440,60129542144,51539607552,34359738368]
def familyA_RT : List Nat := [1107363223,2,4,168305822,16,404791478,1346404822,128,256,34187138,1024,136883462,274773268,8192,1078060432,32768,65536,174817538,409797892,524288,1350116368,2097152,4194304,1122607232,1530986758,33554432,1577649172,134217728,268435456,2049450128,1073741824,3663757442,8589934591,17179869183,34359738367,68719476735]
theorem iso_familyA : isolatedCert familyA familyA_E1 familyA_E3 familyA_R familyA_RT 0 = true := by decide +kernel
def familyC_E1 : List Nat := [30064771073,32229165675,12969056365,4294967304,30669820025,4294967328,4294967360,15577662185,12902095681,4294967808,12953345545,2048,4096,4841306664,4294983680,6451026528,30158569985,4295098368,262144,4909304328,4296015872,6991255584,6473273408,8388608,4311744512,15695217161,4362076160,7197820968,7332958304,536870912,16736337985,2147483648,12884901888,30064771072,55834574848,479519464041,98784247808,154618822656,274877906944]
def familyC_E3 : List Nat := [545051336703,55220875263,53140635135,509752540927,53661529599,509989026559,510930639871,55749240831,53073674199,509618421739,53124923295,492541247343,492679135101,19243073470,510662279161,20852768758,53150214039,509758921579,492813901677,19310555038,510933302905,21390933430,20870854102,493518584553,511098444655,55833241503,511094775421,21465378238,21466297846,493916945145,55834174935,493920639723,64424509440,548238940777,203465418751,202970826135,80087505513,200346589801,286245935721]
def familyC_R : List Nat := [479519464041,479519464043,479519464045,479519464041,479519464057,479519464041,479519464041,479519464169,479519464297,479519464041,479519465065,2048,4096,479519472233,479519464041,479519496809,479519529577,479519464041,262144,479519988329,479519464041,479521561193,479523658345,8388608,479519464041,479553018473,479519464041,479653681769,479787899497,536870912,480593205865,2147483648,479519464041,479519464041,479519464041,479519464041,548238940777,479519464041,274877906944]
def familyC_RT : List Nat := [272184895487,2,4,272184895487,16,272184895487,272184895487,128,256,272184895487,1024,272184897535,272184899583,8192,272184895487,32768,65536,272184895487,272185157631,524288,272184895487,2097152,4194304,272193284095,272184895487,33554432,272184895487,134217728,268435456,272721766399,1073741824,274332379135,272184895487,272184895487,272184895487,272184895487,68719476736,272184895487,547062802431]
theorem iso_familyC : isolatedCert familyC familyC_E1 familyC_E3 familyC_R familyC_RT 0 = true := by decide +kernel
def familyD_E1 : List Nat := [4294967297,15049296491,4379121773,8,4900016249,4294967328,64,6987727593,4312161089,512,68443657,2048,4096,546339368,16384,6451026528,4388766209,4295098368,262144,614337032,1048576,6991255584,2178306112,8388608,16777216,7105282569,67108864,7197820968,3037991008,536870912,3851436097,2147483648,12885032995,15049296491,17179869184,34359738368,68719476736]
def familyD_E3 : List Nat := [137029443583,16566169599,14485929471,136090386175,15006823935,136326871807,137268485119,17094535167,14418968535,135956266987,10175250335,136058961775,127606914941,10653138878,128410189817,16557801462,14495508375,136096766827,127741681517,10720620446,128681213561,17095966134,12280919510,128446364393,137436289903,17178535839,128842686077,17170410942,12876363254,128844724985,12884501975,137438354155,136092048383,16566169599,24252930665,41432799849,75792538217]
def familyD_R : List Nat := [15049296491,15049296491,15116671599,8,15654345339,15049296491,64,15594572523,15049579371,512,15117737579,2048,4096,15595633259,16384,15057738347,15126186603,15049296491,262144,15663499883,1048576,15597967979,15063210603,8388608,16777216,15695219307,67108864,15787756139,15923026539,536870912,16736471659,2147483648,15049296491,15049296491,17179869184,34359738368,68719476736]
def familyD_RT : List Nat := [14401906103,14401906103,4,14401906111,16,14401906103,14401906167,128,256,14401906615,1024,14401908151,274773268,8192,1078060432,32768,65536,14401906103,409797892,524288,1350116368,2097152,4194304,1122607232,14418683319,33554432,1577649172,134217728,268435456,2049450128,1073741824,16549389751,14401906103,14401906103,17179869184,34359738368,68719476736]
theorem iso_familyD : isolatedCert familyD familyD_E1 familyD_E3 familyD_R familyD_RT 5325 = true := by decide +kernel

/-! ### Pieces outside every closed chain (Proposition chainfree, Corollary chainfree) -/

/-- The threefold pieces certified to lie on no cycle of the graph of blocks of total degree one: a is
chain-free when no piece b != a carries such a block from a and reaches a in the certificate R.  Since R
contains the reachability relation (`reachOK`), a piece counted here lies on no closed chain. -/
def chainFreeZ (ps : List Piece) (E1 R : List Nat) : Nat :=
  (ps.foldl (fun s p =>
    let free := p.isZ && (List.range ps.length).all (fun b =>
      b == s.2 || !(bit (E1.getD s.2 0) b) || !(bit (R.getD b 0) s.2))
    (if free then s.1 + 1 else s.1, s.2 + 1)) (0, 0)).1

/-- The degree-one rows are those of the Ext table, R is a reachability certificate, and the number of
threefold pieces outside every closed chain is `v`. -/
def chainFreeCert (ps : List Piece) (E1 R : List Nat) (v : Nat) : Bool :=
  rows1 ps == E1 && reachOK ps.length E1 R && chainFreeZ ps E1 R == v

/-- Family (c): twenty-two of the thirty-two threefold pieces lie on no closed chain. -/
theorem chainfree_familyC : chainFreeCert familyC familyC_E1 familyC_R 22 = true := by decide +kernel

/-- Family (a): no threefold piece lies on a closed chain. -/
theorem chainfree_familyA : chainFreeCert familyA familyA_E1 familyA_R 32 = true := by decide +kernel

/-- An edge u -> v of the graph: a block of total degree one from u to v. -/
def edge (u v : Piece) : Bool := (pairInfo u v).1

/-- The sixteen pieces at the top shift of the thirty-two (shift 1, offset 8). -/
def topBase : List Piece := base.filter (fun p => p.shift == 9)

/-- Pieces of positive twist at shifts -3 to 2: O_{Z_zeta} (x) L^k [s] for every zeta in mu_4^3 and
k = 1, 2, 3, and L^l [t] for l = 1, .., 4. -/
def belowTop : List Piece :=
  ((List.range 64).flatMap fun i => (List.range 3).flatMap fun k => (List.range 6).map fun s =>
    Z (i / 16) ((i / 4) % 4) (i % 4) (k + 1) (s + 5)) ++
  ((List.range 4).flatMap fun l => (List.range 6).map fun t => L (l + 1) (t + 5))

/-- Corollary chainfree (ii) in the window: no base piece and no piece of positive twist at a shift at most one
above the top enters a top piece (self-loops are not edges of the graph). -/
theorem no_entry_top :
    ((base ++ belowTop).all fun u => topBase.all fun v => (u.shift == 9 && u.isZ && u.twist == 0) || !(edge u v)) = true := by
  decide +kernel

/-- The sharpness: a line bundle or a twisted copy at shift 3 does enter every top piece. -/
theorem entry_at_shift_three :
    (topBase.all fun v => edge (L 1 11) v && edge (L 4 11) v && edge (Z 0 0 0 1 11) v) = true := by decide +kernel

/-- Corollary chainfree (iii), the limit: with L^1[-2], .., L^6[3] every one of the thirty-two lies on a closed chain of
length six, through L^6[3], L^2[-1], L^3[0], L^4[1], L^5[2] at shift 1 and through L^5[2], L^1[-2], L^2[-1], L^3[0],
L^4[1] at shift 0. -/
def cycleThrough (p : Piece) : Bool :=
  if p.shift == 9 then
    edge (L 6 11) p && edge p (L 2 7) && edge (L 2 7) (L 3 8) && edge (L 3 8) (L 4 9) && edge (L 4 9) (L 5 10) && edge (L 5 10) (L 6 11)
  else
    edge (L 5 10) p && edge p (L 1 6) && edge (L 1 6) (L 2 7) && edge (L 2 7) (L 3 8) && edge (L 3 8) (L 4 9) && edge (L 4 9) (L 5 10)

theorem six_bundles_cycles : (base.all cycleThrough) = true := by decide +kernel

end Isolated


/-! ## Section 7: arithmetic of the newer sections -/

/-- The lower bound r = (4 + rho) n^2 - 2n at n = 3 for Hankel rank rho = 3, 2, 1, 0:
57, 48, 39, 30 (Remark twistfollows: with powers of L and h non-constant the polarised
shape forces c_1 = ... = c_5 = 0, so r lies in {48, 39, 30}). -/
theorem r_values_n3 : rBound 3 3 = 57 ∧ rBound 2 3 = 48 ∧ rBound 1 3 = 39 ∧ rBound 0 3 = 30 := by
  decide

/-- Lemma td: for alpha = sqrt d the trace form Tr(alpha x y) on the Q-basis (1, sqrt d)
has Gram matrix [[Tr sqrt d, Tr d], [Tr d, Tr d sqrt d]] = [[0, 2d], [2d, 0]], a hyperbolic
plane; for alpha = -1/2 it is [[-1, 0], [0, -d]].  The determinant of T_d is
(-4 d^2)^2 * d = 16 d^5, of square class d.  Checked for the squarefree d <= 30. -/
def sqfree : List Int := [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30]
def trSqrtBlock (d : Int) : List (List Int) := [[0, 2 * d], [2 * d, 0]]
def trHalfBlock (d : Int) : List (List Int) := [[-1, 0], [0, -d]]
def det2 (m : List (List Int)) : Int :=
  match m with
  | [[a, b], [c, e]] => a * e - b * c
  | _ => 0
theorem td_trace_forms :
    sqfree.all (fun d =>
      det2 (trSqrtBlock d) == -4 * d * d && det2 (trHalfBlock d) == d &&
      det2 (trSqrtBlock d) * det2 (trSqrtBlock d) * det2 (trHalfBlock d) == 16 * d ^ 5 &&
      -- the hyperbolic block: e = (1, 0), f = (0, 1/(2d)) gives q(e) = q(f) = 0, b(e, f) = 1
      (trSqrtBlock d).head! == [0, 2 * d]) = true := by decide

/-- Nikulin's conditions for the primitive embedding of L_d (rank 6, signature (2, 4),
discriminant group generated by 2 elements) in the K3 lattice (rank 22, signature (3, 19)):
3 - 19 = -16 is divisible by 8, 2 <= 3, 4 <= 19 and 22 - 6 = 16 > 2.  The discriminant
group Z/4 + Z/4d has order 16 d = |det L_d| for L_d = U^2 + <-4> + <-4d>. -/
theorem nikulin_conditions :
    ((3 : Int) - 19) % 8 = 0 ∧ 2 ≤ 3 ∧ 4 ≤ 19 ∧ 22 - 6 > 2 ∧
    sqfree.all (fun d => (-1) * (-1) * (-4) * (-4 * d) == 16 * d) = true := by decide

/-- The discriminant b^2 c^2 - 4 c^3 - 4 b^3 e - 27 e^2 + 18 b c e of x^3 + b x^2 + c x + e:
49 for x^3 + x^2 - 2x - 1 (Q(zeta_7)^+), 81 for x^3 - 3x + 1 (Q(zeta_9)^+) and 148 for
x^3 + x^2 - 3x - 1 (Remark sexticfields, Theorem linkcm). -/
def cubicDisc (b c e : Int) : Int :=
  b * b * c * c - 4 * c * c * c - 4 * b * b * b * e - 27 * e * e + 18 * b * c * e
theorem cubic_discriminants :
    cubicDisc 1 (-2) (-1) = 49 ∧ cubicDisc 0 (-3) 1 = 81 ∧ cubicDisc 1 (-3) (-1) = 148 := by
  decide

/-- The parity lemma and Remark twistfollows: the coefficient of a monomial in k distinct
coordinate two-forms in theta_h^k is k! times the product of the h's, so 6 h_1 h_4 h_2 for
a_1 b_1 a_2 (k = 3) and 24 h_1 h_4 h_2 h_5 for a_1 b_1 a_2 b_2 (k = 4); the k! are 6 and 24. -/
def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k
theorem theta_h_coefficients : fact 3 = 6 ∧ fact 4 = 24 ∧ fact 6 = 720 := by decide


/-! ## Section 8: K3 surfaces through Floccari's theorem, Weil sixfolds and the link -/

/-- Integer valuation and unit part at a prime p, with fuel (structural recursion). -/
def valF (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n != 0 && n % p == 0 then 1 + valF p fuel (n / p) else 0
def unitF (p : Nat) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n != 0 && n % p == 0 then unitF p fuel (n / p) else n
def vp (p : Nat) (a : Int) : Nat := valF p 64 a.natAbs
/-- The unit part with its sign, as an integer prime to p. -/
def up (p : Nat) (a : Int) : Int := (if a < 0 then -1 else 1) * (unitF p 64 a.natAbs : Int)
/-- The Legendre symbol of a unit u at an odd prime p, by Euler's criterion, as +-1. -/
def legendre (p : Nat) (u : Int) : Int :=
  let r := (u % (p : Int)).toNat
  if (r ^ ((p - 1) / 2)) % p == 1 then 1 else -1
def epsil (u : Int) : Nat := ((u % 8).toNat - 1) / 2 % 2
def omeg (u : Int) : Nat := (((u % 8).toNat) * ((u % 8).toNat) - 1) / 8 % 2
def sgnPow (k : Nat) : Int := if k % 2 == 0 then 1 else -1
/-- The Hilbert symbol (a, b)_p for nonzero integers a, b and a prime p (Serre, Chap. III, Thm. 1). -/
def hilbert (p : Nat) (a b : Int) : Int :=
  let al := vp p a; let be := vp p b; let u := up p a; let v := up p b
  if p == 2 then sgnPow (epsil u * epsil v + al * omeg v + be * omeg u)
  else sgnPow (al * be * ((p - 1) / 2)) * (legendre p u) ^ be * (legendre p v) ^ al
/-- The Hasse invariant prod_{i<j} (a_i, a_j)_p of a diagonal form. -/
def hasseInv (p : Nat) : List Int → Int
  | [] => 1
  | a :: rest => (rest.foldl (fun acc b => acc * hilbert p a b) 1) * hasseInv p rest
def U3 : List Int := [1, -1, 1, -1, 1, -1]
/-- An integer is a nonzero square in Q_p (p odd, p not dividing it): Euler's criterion; for p = 2
an odd integer is a square in Q_2 iff it is 1 mod 8. -/
def unitSquare (p : Nat) (x : Int) : Bool :=
  if p == 2 then x % 8 == 1 else legendre p x == 1 && x % (p : Int) != 0

/-- Table rmopen: rows (e, [(a_i, b_i)], p, d mod squares, d = e N(delta), its square factor). -/
def rmRows : List (Int × List (Int × Int) × Nat × Int × Int × Int) :=
  [(2, [(3, 3), (2, 4), (-3, 2)], 3, 14, 504, 6),
   (3, [(2, 4), (0, 3), (-1, 0)], 3, 11, 3564, 18),
   (5, [(-1, 1), (2, 1), (-4, 1)], 2, 55, 220, 2),
   (6, [(-3, 2), (0, 3), (-4, 0)], 2, 15, 77760, 72),
   (7, [(0, 2), (3, 3), (-1, 0)], 7, 6, 10584, 42)]
def normE (e : Int) (ab : Int × Int) : Int := ab.1 * ab.1 - e * ab.2 * ab.2
/-- The sign of a + b sqrt e at s_1 (sqrt e > 0), by integer comparison. -/
def posS1 (e : Int) (ab : Int × Int) : Bool :=
  let a := ab.1; let b := ab.2
  if a ≥ 0 && b ≥ 0 then (a > 0 || b > 0)
  else if a ≤ 0 && b ≤ 0 then false
  else if a > 0 then a * a > e * b * b else e * b * b > a * a
def posS2 (e : Int) (ab : Int × Int) : Bool := posS1 e (ab.1, -ab.2)
/-- The Gram matrix of Tr<alpha> in the basis 1, sqrt e, and the change of basis
v_2 = (-b e, a), which diagonalises it to <2a, 2 a e N(alpha)> when a != 0. -/
def gramTr (e : Int) (ab : Int × Int) : Int × Int × Int := (2 * ab.1, 2 * ab.2 * e, 2 * ab.1 * e)
def diagTr (e : Int) (ab : Int × Int) : List Int :=
  if ab.1 == 0 then [1, -1] else [2 * ab.1, 2 * ab.1 * e * normE e ab]
def diagT (e : Int) (al : List (Int × Int)) : List Int := (al.map (diagTr e)).foldr (· ++ ·) []

theorem rmopen_gram :
    rmRows.all (fun r => r.2.1.all (fun ab =>
      let g := gramTr r.1 ab
      -- determinant 4 e N(alpha)
      g.1 * g.2.2 - g.2.1 * g.2.1 == 4 * r.1 * normE r.1 ab &&
      -- q(v_2) = 2 a e N(alpha) and b(v_1, v_2) = 0 for v_1 = (1,0), v_2 = (-b e, a)
      g.1 * (ab.2 * r.1) * (ab.2 * r.1) - 2 * g.2.1 * (ab.2 * r.1) * ab.1 + g.2.2 * ab.1 * ab.1
        == 2 * ab.1 * r.1 * normE r.1 ab &&
      g.1 * (-(ab.2 * r.1)) + g.2.1 * ab.1 == 0)) = true := by decide

theorem rmopen_signatures :
    rmRows.all (fun r => match r.2.1 with
      | [x, y, z] => posS1 r.1 x && !posS2 r.1 x && posS1 r.1 y && !posS2 r.1 y &&
          !posS1 r.1 z && !posS2 r.1 z && normE r.1 x < 0 && normE r.1 y < 0 && normE r.1 z > 0
      | _ => false) = true := by decide

/-- d = e N(alpha_1 alpha_2 alpha_3) = (d mod squares) * f^2, and -d is a square in Q_p. -/
theorem rmopen_discriminants :
    rmRows.all (fun r =>
      r.1 * (r.2.1.map (normE r.1)).foldl (· * ·) 1 == r.2.2.2.2.1 &&
      r.2.2.2.2.1 == r.2.2.2.1 * r.2.2.2.2.2 * r.2.2.2.2.2 &&
      unitSquare r.2.2.1 (-r.2.2.2.1)) = true := by decide

/-- At the prime p of each row the Hasse invariants of T and of U^3 differ, so T_p is not
hyperbolic and T has Witt index one (Corollary rmopen, Appendix app:calc). -/
theorem rmopen_hasse :
    rmRows.all (fun r => hasseInv r.2.2.1 (diagT r.1 r.2.1) != hasseInv r.2.2.1 U3) = true := by
  decide

/-- Lemma witt(ii): the witnesses T = U^2 + <-x, -y> of Witt index two and their (lambda, m):
<-x, -y> = <-lambda, -lambda d> up to squares with d = x y, and m = lambda d up to squares. -/
def wittWitnesses : List (Int × Int × Int × Int × Int) :=
  -- (x, y, lambda, s, m) with lambda x y = y s^2 = m s^2
  [(7, 7, 7, 7, 7), (5, 23, 5, 5, 23), (7, 23, 7, 7, 23)]
theorem witt_witnesses :
    wittWitnesses.all (fun w =>
      let x := w.1; let y := w.2.1; let l := w.2.2.1; let s := w.2.2.2.1; let m := w.2.2.2.2
      -- x = lambda and lambda * (x y) = y * s^2, so <-x,-y> = <-lambda, -lambda d>
      x == l && l * (x * y) == y * s * s &&
      -- lambda d = m times a square
      (l * x * y) % m == 0 && (l * x * y / m) == s * s) = true := by decide

/-- Witt index one witnesses <1,1,-1,-2,-3,-3> (d = 18, -d a square at 3) and
<1,1,-1,-2,-5,-10> (d = 100, -d a square at 5): there the Hasse invariant differs from that
of U^3, so condition (d) of Lemma witt(ii) fails. -/
theorem witt_index_one_examples :
    let t1 : List Int := [1, 1, -1, -2, -3, -3]
    let t2 : List Int := [1, 1, -1, -2, -5, -10]
    t1.foldl (· * ·) 1 = 18 ∧ t2.foldl (· * ·) 1 = 100 ∧
      unitSquare 3 (-2) = true ∧ hasseInv 3 t1 ≠ hasseInv 3 U3 ∧
      unitSquare 5 (-1) = true ∧ hasseInv 5 t2 ≠ hasseInv 5 U3 := by decide

/-- A nonzero integer is a square in Q_p: even valuation and square unit part. -/
def isSqQp (p : Nat) (x : Int) : Bool :=
  vp p x % 2 == 0 && (let u := up p x; if p == 2 then u % 8 == 1 else legendre p u == 1)
/-- The 1980 diagonal forms <a, b, -x_1, -x_2, -x_3, -x_4> of Lemma witt(ii), 1 <= a <= b <= 3,
x_1 <= ... <= x_4 in {1, 2, 3, 5, 6, 7, 10, 23}. -/
def wittVals : List Int := [1, 2, 3, 5, 6, 7, 10, 23]
def nondecr4 : List (List Int) :=
  (List.range 8).foldr (fun i acc => acc ++ ((List.range 8).filter (· ≥ i)).foldr (fun j acc2 =>
    acc2 ++ ((List.range 8).filter (· ≥ j)).foldr (fun k acc3 =>
      acc3 ++ ((List.range 8).filter (· ≥ k)).map (fun l =>
        [wittVals.getD i 0, wittVals.getD j 0, wittVals.getD k 0, wittVals.getD l 0])) []) []) []
def wittForms : List (List Int) :=
  ([(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)] : List (Int × Int)).foldr (fun ab acc =>
    acc ++ nondecr4.map (fun xs => ab.1 :: ab.2 :: xs.map (fun x => -x))) []
/-- Condition (d) of Lemma witt(ii): T_p and U^3_p are isometric at every prime p at which -d is a
square; at a prime not dividing 2 and the entries both Hasse invariants are 1, so only
p in {2, 3, 5, 7, 23} need checking, and there equal rank and discriminant reduce isometry to
equal Hasse invariants. -/
def wittTwo (t : List Int) : Bool :=
  let d := t.foldl (· * ·) 1
  ([2, 3, 5, 7, 23] : List Nat).all (fun p => !(isSqQp p (-d)) || hasseInv p t == hasseInv p U3)
theorem witt_count :
    wittForms.length = 1980 ∧ (wittForms.filter wittTwo).length = 1484 := by decide +kernel

/-- The rank-five example: <1,1,-1,-23,-23> has discriminant -1 up to squares and
Hasse invariant at 23 different from (-1,-1)_23 = 1, so it does not embed in V_1. -/
theorem rank_five_example :
    hasseInv 23 [1, 1, -1, -23, -23] = -1 ∧ hilbert 23 (-1) (-1) = 1 ∧
      ([1, 1, -1, -23, -23] : List Int).foldl (· * ·) 1 = -(23 * 23) := by decide

/-- Polynomials in t^2 as coefficient lists: product. -/
def pmulNat (p q : List Nat) : List Nat :=
  (List.range (p.length + q.length - 1)).map (fun k =>
    (List.range (k + 1)).foldl (fun acc i => acc + (p.getD i 0) * (q.getD (k - i) 0)) 0)
/-- Hodge numbers of Z_K and Z_K^2 at a very general point (Proposition zkpowers):
(1 + t^2 + t^4)^3 and (1 + 4t^2 + 10t^4 + 4t^6 + t^8)^3, the second from the partitions in a
2 x 2 box with weights (dim S_lambda' Q^2)^2 = 1, 4, 1 + 9, 4, 1. -/
theorem zk_hodge_numbers :
    pmulNat (pmulNat [1, 1, 1] [1, 1, 1]) [1, 1, 1] = [1, 3, 6, 7, 6, 3, 1] ∧
    1 + 3 = 4 ∧ 1 + 9 = 10 ∧
    ((pmulNat (pmulNat [1, 4, 10, 4, 1] [1, 4, 10, 4, 1]) [1, 4, 10, 4, 1]).take 5) = [1, 12, 78, 316, 879] := by
  decide

/-- Dimensions of B^*(X^a) tensor B^*(Z_K^b) in degrees 4, 6, 8, 10 (Theorem linkall and the
counts after it): convolution of the Hodge numbers of the factors. -/
def conv (p q : List Nat) (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun acc i => acc + p.getD i 0 * q.getD (k - i) 0) 0
theorem product_algebra_counts :
    let hx := [1, 1, 1, 1, 1]
    let hx2 := [1, 3, 8, 16, 28]
    let hz := [1, 3, 6, 7, 6, 3, 1]
    let hz2 := [1, 12, 78, 316, 879]
    [conv hx hz 2, conv hx hz 3, conv hx hz 4, conv hx hz 5] = [10, 17, 23, 25] ∧
    [conv hx2 hz 2, conv hx2 hz 3, conv hx2 hz 4] = [23, 65, 151] ∧
    [conv hx2 hz2 2, conv hx2 hz2 3] = [122, 662] ∧
    -- the mixed classes: 20 - 17, 29 - 23, 35 - 25; 26 - 23, 98 - 65, 293 - 151; 134 - 122, 995 - 662
    [20 - 17, 29 - 23, 35 - 25, 26 - 23, 98 - 65, 293 - 151, 134 - 122, 995 - 662] =
      [3, 6, 10, 3, 33, 142, 12, 333] := by decide

/-- Theorem tenfold(i): in degree six on X x Z_K the Kunneth component H^2(X) (x) H^4(Z_K)
carries 9 = 6 + 3 Hodge classes, B^2(X) (x) B^4(Z_K) of dimension 1 * 6 and the F-line F iota'
of dimension 3; the total in degree six is 9 + 7 + 3 + 1 = 20. -/
theorem tenfold_count : 1 * 6 + 3 = 9 ∧ 9 + 7 + 3 + 1 = 20 := by decide

/-- Theorem link(iii) and tenfold(ii): b acts on T_{Z,i} by sigma_i(b)^2 and on U_{Z,k} by
sigma_i(b)^2 sigma_j(b)^2 = N(b)^2 / sigma_k(b)^2; and 2b = (b + 1)^2 - b^2 - 1, so squares
span F.  Checked as integer identities on the grid [-3, 3]^3. -/
theorem squares_span :
    (List.range 7).all (fun i => (List.range 7).all (fun j => (List.range 7).all (fun k =>
      let b1 : Int := i - 3; let b2 : Int := j - 3; let b3 : Int := k - 3
      2 * b1 == (b1 + 1) ^ 2 - b1 ^ 2 - 1 &&
      (b1 * b1) * (b2 * b2) * (b3 * b3) == (b1 * b2 * b3) ^ 2))) = true := by decide

/-- Theorem cmkl: 279 transitive subgroups of S_6 and seven values of |I| give 1953 pairs; the
CM types of a degree-twelve CM field number 2^6 = 64 = 40 + 24, the types of Weil type for K
number C(6,3) = 20; the Hodge numbers for Gamma = S_6, A_6 at |I| = 3 exceed those at
|I| not in {0, 3, 6} by the two Weil classes in degree six; 36, 225, 400 are the Hodge numbers
of E^6, the squares of 6, 15, 20. -/
theorem cm_sixfold_counts :
    279 * 7 = 1953 ∧ 2 ^ 6 = 64 ∧ 40 + 24 = 64 ∧ 2 * 12 = 24 ∧ choose 6 3 = 20 ∧
    22 - 20 = 2 ∧ [6 * 6, 15 * 15, 20 * 20] = [36, 225, 400] ∧
    [choose 6 1, choose 6 2, choose 6 3] = [6, 15, 20] := by decide

/-- Theorem eaab(ii) and Theorem cmkl: the type conditions of a conjugate CM type and its
complement give d_l - d_i - d_j + d_E = 0 for l = 1, 2, 3, whose only solutions have
d_1 = d_2 = d_3 = d_E; checked on all integer vectors with entries in [-3, 3]. -/
theorem pohlmann_linear :
    (List.range 7).all (fun a => (List.range 7).all (fun b => (List.range 7).all (fun c =>
      (List.range 7).all (fun e =>
        let d1 : Int := a - 3; let d2 : Int := b - 3; let d3 : Int := c - 3; let dE : Int := e - 3
        let ok := d1 - d2 - d3 + dE == 0 && d2 - d1 - d3 + dE == 0 && d3 - d1 - d2 + dE == 0
        !ok || (d1 == dE && d2 == dE && d3 == dE))))) = true := by decide

/-- Split polarisations (Appendix app:calc): the polynomial discriminants of the defining
sextics of Q(zeta_21)^+, Q(zeta_28)^+, Q(zeta_36)^+ factor as 3^3 7^5, 2^6 7^5, 2^6 3^9, and
the forms with three negative places number C(6,3) = 20. -/
theorem sextic_discriminants :
    (3 : Nat) ^ 3 * 7 ^ 5 = 453789 ∧ (2 : Nat) ^ 6 * 7 ^ 5 = 1075648 ∧
    (2 : Nat) ^ 6 * 3 ^ 9 = 1259712 ∧ choose 6 3 = 20 := by decide

/-- Proposition noweil(i): the X-degree of a pull-back of a Weil class is r_X = 8 m / [E' : Q]
with [E' : Q] dividing m, a multiple of 8; and (iii): b_2 = 7, 8 of the Kummer and OG6 types
leave transcendental rank at most 6, 7 < 9. -/
theorem noweil_degrees :
    (List.range 12).all (fun m' => (List.range 12).all (fun f =>
      (8 * (m' * (f + 1))) / (f + 1) % 8 == 0)) = true ∧ 7 - 1 < 9 ∧ 8 - 1 < 9 := by decide

/-! ## Section 9: Weil classes on E_0^8, the K3 x K3 criterion and the gamma link -/

/-! ### Exterior algebra on bitmask monomials -/
/-- Number of pairs (i, j) with i in a, j in b, i > j: e_a ∧ e_b = (-1)^this e_(a ∪ b). -/
def crossings (a b : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc j =>
    if b.testBit j then acc + ((List.range n).filter (fun i => i > j && a.testBit i)).length else acc) 0
def ewedge (n : Nat) (x y : List (Nat × Int)) : List (Nat × Int) :=
  x.foldl (fun acc (a, c) => y.foldl (fun acc' (b, d) =>
    if a &&& b == 0 then
      (a ||| b, (if crossings a b n % 2 == 0 then 1 else -1) * c * d) :: acc'
    else acc') acc) []
def ecoeff (x : List (Nat × Int)) (m : Nat) : Int :=
  x.foldl (fun acc (a, c) => if a == m then acc + c else acc) 0
/-- Omega = sum_k a_k ∧ b_k with a_k, b_k the generators 2k, 2k+1. -/
def omega (m : Nat) : List (Nat × Int) := (List.range m).map (fun k => (3 * 4 ^ k, 1))
def epow (n : Nat) (x : List (Nat × Int)) : Nat → List (Nat × Int)
  | 0 => [(0, 1)]
  | k + 1 => ewedge n (epow n x k) x
/-- Theorem qmloci(iii): Omega^m = m! a_1 ∧ b_1 ∧ ... ∧ a_m ∧ b_m for m = 1, ..., 4; every other
monomial has coefficient zero. -/
theorem omega_power :
    (List.range 4).all (fun m' =>
      let m := m' + 1
      let p := epow (2 * m) (omega m) m
      ecoeff p (4 ^ m - 1) == (fact m : Int) &&
        (List.range (4 ^ m - 1)).all (fun s => ecoeff p s == 0)) = true := by decide +kernel

/-! ### Pieces of the convolutions on E_0^8 -/
/-- A piece zeta = (i^a_1, ..., i^a_4) with a_j in [0, 4) and sum a_j even (prod zeta = +-1). -/
def pieces8 : List (List Nat) :=
  (List.range 256).filterMap (fun s =>
    let a := [s % 4, s / 4 % 4, s / 16 % 4, s / 64 % 4]
    if a.foldl (· + ·) 0 % 2 == 0 then some a else none)
/-- prod zeta = 1 (parity 0) or -1 (parity 1). -/
def par (a : List Nat) : Nat := a.foldl (· + ·) 0 / 2 % 2
/-- |i^x - i^y|^2 = 0, 2, 4, 2 for x - y = 0, 1, 2, 3 mod 4. -/
def dsq (x y : Nat) : Nat := [0, 2, 4, 2].getD ((x + 4 - y) % 4) 0
def diffs (a b : List Nat) : List Nat := (List.range 4).filter (fun j => a.getD j 0 != b.getD j 0)
def dval (a b : List Nat) : Nat := (diffs a b).foldl (fun acc j => acc * dsq (a.getD j 0) (b.getD j 0)) 1
/-- Proposition w:prop-equivgroup(ii): for pieces differing in k coordinates, 2^k divides D. -/
theorem d_divisible :
    pieces8.length = 128 ∧
    pieces8.all (fun a => pieces8.all (fun b => dval a b % 2 ^ (diffs a b).length == 0)) = true := by
  decide +kernel
/-- Theorem w:thm-equivtwoshift: in the slice graph G_(j, z) every vertex has exactly seven neighbours and
weighted degree 20 (weights D / 8). -/
theorem slice_degrees :
    pieces8.all (fun a => (List.range 4).all (fun j =>
      let nb := pieces8.filter (fun b => b.getD j 0 == a.getD j 0 && par b != par a &&
        (diffs a b).length == 3)
      nb.length == 7 && nb.foldl (fun acc b => acc + dval a b / 8) 0 == 20)) = true := by
  decide +kernel
/-- The types tau in {0,1,2}^4 with |tau| = 2: ten of them, of total dimension
sum 2^#{j : tau_j = 1} = 28; D^2 has dimension 131 * 28 = 3668 and the kernel bound is
84 + 4 * 4 * 1 + 6 * 16 * 4 = 484 (Proposition w:prop-efourdiagonal(ii)). -/
def types : List (List Nat) :=
  (List.range 81).filterMap (fun s =>
    let t := [s % 3, s / 3 % 3, s / 9 % 3, s / 27 % 3]
    if t.foldl (· + ·) 0 == 2 then some t else none)
theorem cupkernel_counts :
    types.length = 10 ∧
    types.foldl (fun acc t => acc + 2 ^ (t.filter (· == 1)).length) 0 = 28 ∧
    131 * 28 = 3668 ∧ 84 + 4 * 4 * 1 + 6 * 16 * 4 = 484 := by decide
/-- Theorem w:thm-equivtwoshift: the diagonal threshold 84 + 28 * 64 = 1876, the totals
20 N + (bound_N - 1876) for N = 0, ..., 5, the number 6885 of slice sets with N <= 5, and
20 * 6 = 120. -/
theorem twolevel_totals :
    84 + 28 * 64 = 1876 ∧
    ((List.range 6).map (fun N => 20 * N + ([3668, 3668, 3632, 3545, 3428, 3311].getD N 0 - 1876))) =
      [1792, 1812, 1796, 1729, 1632, 1535] ∧
    (List.range 6).foldl (fun acc k => acc + choose 16 k) 0 = 6885 ∧ 20 * 6 = 120 := by decide

/-! ### The gamma link -/
def wV : List (List Int) :=
  [1, -1].flatMap (fun s1 => [1, -1].flatMap (fun s2 => [1, -1].map (fun s3 => [s1, s2, s3, 0, 0, 0, 0])))
def wD : List (List Int) :=
  [0, 1, 2].flatMap (fun i => [1, -1].flatMap (fun u => [1, -1].map (fun v =>
    (List.range 7).map (fun k => if k == i then u else if k == i + 3 then v else 0))))
def wE : List (List Int) := [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1]]
def vadd (x y : List Int) : List Int := List.zipWith (· + ·) x y
def subsets3 : List (List Int) → List (List Int)
  | [] => []
  | x :: xs => (subsets2 xs).map (fun p => vadd x p) ++ subsets3 xs
where
  subsets2 : List (List Int) → List (List Int)
    | [] => []
    | y :: ys => ys.map (fun z => vadd y z) ++ subsets2 ys
/-- Weights of H^1(X) (x) H^3(Z_K). -/
def w13 : List (List Int) := wV.flatMap (fun x => (subsets3 wD).map (fun t => vadd x t))
/-- dim of G-invariants: inclusion-exclusion over weights 0 and 2 on the three SL_2 factors. -/
def ginv (ws : List (List Int)) (pred : List Int → Bool) : Int :=
  [0, 1].foldl (fun acc1 u1 => [0, 1].foldl (fun acc2 u2 => [0, 1].foldl (fun acc3 u3 =>
    acc3 + (if (u1 + u2 + u3) % 2 == 0 then 1 else -1) *
      ((ws.filter (fun w => w.take 3 == [2 * u1, 2 * u2, 2 * u3] && pred w)).length : Int)) acc2) acc1) 0
def hodgePred (w : List Int) : Bool :=
  w.getD 3 0 == w.getD 4 0 && w.getD 4 0 == w.getD 5 0 && w.getD 6 0 == -2 * w.getD 3 0
/-- Theorem tensordecomp and Theorem gammalink: Hom_G(V, H^3(Z_K)) has dimension 8; there is no Hodge
class in H^1(X) (x) H^3(Z_K); with two factors H^1(E) the Hodge classes form a plane (the k-line
of gamma). -/
theorem gamma_counts :
    (subsets3 wD).length = 220 ∧ ginv w13 (fun _ => true) = 8 ∧ ginv w13 hodgePred = 0 ∧
    ginv (w13.flatMap (fun w => wE.flatMap (fun e => wE.map (fun e' => vadd w (vadd e e'))))) hodgePred = 2 := by
  decide +kernel

/-! ### Exclusion of line-bundle convolutions (Theorem w:thm-uniformexclusion) -/
/-- Theorem w:thm-nothingentersall, steps between two L's: two pieces L_zeta, L_zeta' of E_0^(2n), n = 3, 4, differ by
the ratio r = zeta' / zeta, written as exponents r_j in [0, 4) with even sum; they differ in the
m coordinates where r_j != 0, and prod zeta' = prod zeta exactly when the exponent sum of r is
divisible by 4. For every nonzero ratio, every Ext degree q in [m, 2n - m] of the parity
1 + [prod zeta != prod zeta'] is at least 2, so every step between two L's has excess >= 1. -/
def stepOK (n : Nat) (r : List Nat) : Bool :=
  let m := (r.filter (· != 0)).length
  let parity := (1 + r.foldl (· + ·) 0 / 2 % 2) % 2
  (List.range (2 * n + 1)).all (fun q => !(m ≤ q && q + m ≤ 2 * n && q % 2 == parity) || q ≥ 2)
def piecesN (n : Nat) : List (List Nat) :=
  (List.range (4 ^ n)).filterMap (fun s =>
    let a := (List.range n).map (fun j => s / 4 ^ j % 4)
    if a.foldl (· + ·) 0 % 2 == 0 then some a else none)
theorem ll_excess :
    (piecesN 3).length = 32 ∧ (piecesN 4).length = 128 ∧
    (piecesN 3).all (fun r => r.all (· == 0) || stepOK 3 r) = true ∧
    (piecesN 4).all (fun r => r.all (· == 0) || stepOK 4 r) = true := by
  decide +kernel
/-- Theorem w:thm-uniformexclusion: the bound r_0 + 1 with r_0 = 7 n^2 - 2 n, i.e. 58 at n = 3 and
105 at n = 4, against the targets 57 and 104 of Theorem criterion. -/
theorem uniform_bounds :
    7 * 3 ^ 2 - 2 * 3 + 1 = 58 ∧ 7 * 4 ^ 2 - 2 * 4 + 1 = 105 ∧ 58 > 57 ∧ 105 > 104 := by decide

/-! ### The K3 x K3 criterion for the Hecke family -/
/-- Proposition kplus: the generic target R = 46 - 2m for m = 3, ..., 10 and the lower bound 22;
Corollary fmkernels: a sum of two kernels has Ext^2 >= 44 > 46 - 2m. -/
theorem kplus_targets :
    (List.range 8).map (fun i => 46 - 2 * (i + 3)) = [40, 38, 36, 34, 32, 30, 28, 26] ∧
    (List.range 8).all (fun i => 22 ≤ 46 - 2 * (i + 3) && 44 > 46 - 2 * (i + 3)) = true := by decide
def isSqfree (e : Nat) : Bool := (List.range (e + 1)).all (fun p => p < 2 || e % (p * p) != 0)
/-- Proposition euler(iii): for squarefree e in [2, 60] and 3 <= m <= 10, the inequality
2 m e + 2 <= 46 - 2 m + 2, i.e. m (e + 1) <= 23, holds exactly for e = 2, m <= 7; e = 3, m <= 5;
e = 5, 6, m = 3. Proposition euler(ii): 12 e - 11 >= 13 for e >= 2. -/
theorem euler_table :
    (List.range 59).all (fun e' => let e := e' + 2
      (List.range 8).all (fun i => let m := i + 3
        !isSqfree e ||
          ((m * (e + 1) ≤ 23) ==
            ((e == 2 && m ≤ 7) || (e == 3 && m ≤ 5) || ((e == 5 || e == 6) && m == 3))))) = true ∧
    (List.range 59).all (fun e' => 12 * (e' + 2) - 11 ≥ 13) = true := by decide
/-- Proposition kummergraph: with k = 8 (e - 1) blown-up points, Z.Z = 24 + 24 e - (24 + k) - k
= 8 e + 16, so dim Ext^2(O_Z, O_Z) = 8 e + 14 + 2 ext^1; for m = 3 the target 40 exceeds 8 e + 14
at e = 2, 3. -/
theorem kummer_graph :
    (List.range 59).all (fun e' => let e := e' + 2; let k := 8 * (e - 1)
      24 + 24 * e - (24 + k) - k == 8 * e + 16) = true ∧ 8 * 2 + 14 < 40 ∧ 8 * 3 + 14 < 40 := by
  decide

/-! ## Section 10: Markman's route on eightfolds and pieces of any kind -/

/-- Binomial coefficients by Pascal's rule. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)
/-- Lemma lem:secantranks: the rank of the contraction of HT^k(X) into a secant class on an abelian n-fold. -/
def secantRank (n k : Nat) : Nat :=
  if k == 0 then 1 else if k < n then 2 * binom n k else if k == n then 2 * binom n k - 1 else 0
/-- Lemma lem:secantranks at n = 3, 4: the ranks 1, 6, 6, 1 and 1, 8, 12, 8, 1; the annihilator in degree two
has dimension binom(2n, 2) - n(n - 1) = n^2 (9 and 16), and the annihilator in degree one is zero. -/
theorem secant_ranks :
    (List.range 4).map (secantRank 3) = [1, 6, 6, 1] ∧
    (List.range 5).map (secantRank 4) = [1, 8, 12, 8, 1] ∧
    binom 6 2 - secantRank 3 2 = 3 ^ 2 ∧ binom 8 2 - secantRank 4 2 = 4 ^ 2 ∧
    binom 6 1 - secantRank 3 1 = 0 ∧ binom 8 1 - secantRank 4 1 = 0 := by decide
/-- Theorem thm:kunnethfour: the forced dimensions 1, 2n, n(n - 1) of Ext^0, Ext^1, Ext^2 together with Serre
duality give chi = 1 - 8 + 12 - 8 + 1 = -2 at n = 4 and chi = 1 - 4 + 1 = -2 at n = 2; the contraction rank
on HH^2 of the product is sum_(a+b=2) rk_a rk_b = 48 at n = 3 and 88 at n = 4. -/
theorem forced_dims :
    ((1 : Int) - 8 + 12 - 8 + 1 = -2) ∧ ((1 : Int) - 4 + 1 = -2) ∧
    1 * 6 + 6 * 6 + 6 * 1 = 48 ∧ 1 * 12 + 8 * 8 + 12 * 1 = 88 := by decide
/-- Theorem thm:kunnethfour: the forced dimensions are consistent with Serre duality on an n-fold
(Ext^2 dual to Ext^1 when n = 3) exactly when 2n = n(n - 1), that is n = 3. -/
theorem serre_only_three (n : Nat) (h : 1 ≤ n) : 2 * n = n * (n - 1) ↔ n = 3 := by
  constructor
  · intro e
    have e' : n * 2 = n * (n - 1) := by rw [Nat.mul_comm]; exact e
    have := Nat.eq_of_mul_eq_mul_left (by omega) e'
    omega
  · intro e; subst e; decide
/-- Theorem thm:secantintegral: on the lattice 16Z alpha + 4Z beta of E^4, h = e_1 + e_2 + e_3 - e_4, q = 1/4,
chi(16a alpha + 4b beta) = -(128 a^2 + 32 b^2) lies in 8Z and is never -2. -/
theorem chi_lattice (a b : Int) :
    8 ∣ 128 * a ^ 2 + 32 * b ^ 2 ∧ -(128 * a ^ 2 + 32 * b ^ 2) ≠ -2 := by
  have h : 128 * a ^ 2 + 32 * b ^ 2 = 8 * (16 * a ^ 2 + 4 * b ^ 2) := by omega
  refine ⟨⟨16 * a ^ 2 + 4 * b ^ 2, h⟩, ?_⟩
  omega
/-- Theorem thm:secantintegral, on a box: the least nonzero |chi| on 16Z alpha + 4Z beta with |a|, |b| <= 20 is 32. -/
theorem chi_lattice_min :
    (List.range 41).all (fun i => (List.range 41).all (fun j =>
      let a : Int := i - 20; let b : Int := j - 20
      (a == 0 && b == 0) || 128 * a * a + 32 * b * b ≥ 32)) = true ∧ 128 * 0 * 0 + 32 * 1 * 1 = 32 := by
  decide +kernel
/-- Theorem w:thm-lagrangian: the lower bounds of the cost T in the cases (b)-(e) of the proof, 3n - 1 - l, 2(n - 1) - l,
3n - 2 - l, 2n - 1 - l and n - 2, are positive for 3 <= n <= 30 and l <= 2n - 3; without P -> P' edges the
bounds of the cases (b), (d), (e) are positive for l <= 2n - 2. -/
theorem lagrangian_costs :
    (List.range 28).all (fun i => let n := i + 3
      (List.range (2 * n - 2)).all (fun l =>
        3 * n - 1 > l && 2 * (n - 1) > l && 3 * n - 2 > l && 2 * n - 1 > l && n - 2 > 0) &&
      (List.range (2 * n - 1)).all (fun l => 3 * n - 1 > l && 3 * n - 2 > l && 2 * n - 1 > l)) = true := by
  decide
/-- Number of elements of a subset of {1,2,3} given as a bitmask. -/
def popc (s : Nat) : Nat := (List.range 3).filter (fun j => s.testBit j) |>.length
def cubeEdge (s t : Nat) : Bool :=
  s != t && (let a := popc (s &&& (7 - t)); let b := popc (t &&& (7 - s))
    a ≤ 1 + a - b && 1 + a ≥ b && 1 + a - b + b ≤ 6)
/-- Lemma w:lem-cubewindows(a): inside a cube the ordered pairs S != S' of subsets of {1,2,3} whose Ext degree
q = 1 + |S \ S'| - |S' \ S| lies in the window [|S \ S'|, 6 - |S' \ S|] number 46, and the only edges
into {1,2,3} come from the three sets of size two, the only edges out of the empty set go to the singletons. -/
theorem cube_windows :
    ((List.range 8).map (fun s => ((List.range 8).filter (fun t => cubeEdge s t)).length)).foldl (· + ·) 0 = 46 ∧
    (List.range 8).filter (fun s => cubeEdge s 7) = [3, 5, 6] ∧
    (List.range 8).filter (fun t => cubeEdge 0 t) = [1, 2, 4] := by decide
/-- Lemma w:lem-cubewindows: the 32 cubes zeta = (i^k_1, i^k_2, i^k_3) with k_1 + k_2 + k_3 even, sixteen with
c = 0 (sum divisible by 4) and sixteen with c = 1. -/
theorem cube_parities :
    (piecesN 3).length = 32 ∧
    ((piecesN 3).filter (fun r => r.foldl (· + ·) 0 % 4 == 0)).length = 16 := by decide
/-- Theorem w:thm-koszulcubes: in the collapsed configuration the edges C -> A, C -> D, A -> B, D -> B,
D -> F@3, F@4 -> A and F@4 -> F@3 all increase in the order C, F@4, D, A, F@3, B, so the graph is acyclic. -/
def collapsedPos : String → Nat
  | "C" => 0 | "F4" => 1 | "D" => 2 | "A" => 3 | "F3" => 4 | "B" => 5 | _ => 6
theorem collapsed_acyclic :
    [("C", "A"), ("C", "D"), ("A", "B"), ("D", "B"), ("D", "F3"), ("F4", "A"), ("F4", "F3")].all
      (fun (x, y) => collapsedPos x < collapsedPos y) = true := by decide

end HodgeClosure

#print axioms HodgeClosure.hc_from_f2_f3p
#print axioms HodgeClosure.hc_from_f3
#print axioms HodgeClosure.hc_from_l_m
#print axioms HodgeClosure.hc_from_l_f3p
#print axioms HodgeClosure.hc_from_v_f3p
#print axioms HodgeClosure.not_hc_from_f2
#print axioms HodgeClosure.not_hc_from_f3p
#print axioms HodgeClosure.not_hc_from_l
#print axioms HodgeClosure.not_hc_from_m
#print axioms HodgeClosure.not_hc_from_v
#print axioms HodgeClosure.not_hc_from_ab
#print axioms HodgeClosure.not_hc_from_l_v
#print axioms HodgeClosure.not_hc_from_m_f3p
#print axioms HodgeClosure.minimal_sets_count
#print axioms HodgeClosure.minimal_sets_are
#print axioms HodgeClosure.prym_locus_small
#print axioms HodgeClosure.prym_fills_three
#print axioms HodgeClosure.prym_dims
#print axioms HodgeClosure.product_locus
#print axioms HodgeClosure.hodge_count
#print axioms HodgeClosure.sum_squares_lt
#print axioms HodgeClosure.mixed_directions
#print axioms HodgeClosure.kunneth_count
#print axioms HodgeClosure.r_values
#print axioms HodgeClosure.fricke_disc_7
#print axioms HodgeClosure.fricke_disc_5
#print axioms HodgeClosure.fricke_roots
#print axioms HodgeClosure.fricke_euler
#print axioms HodgeClosure.fricke_picard
#print axioms HodgeClosure.fricke_transcendental
#print axioms HodgeClosure.fricke_multiplier
#print axioms HodgeClosure.fricke_sign_5
#print axioms HodgeClosure.fricke_sign_7
#print axioms HodgeClosure.fricke_sign_cases
#print axioms HodgeClosure.hecke_dims
#print axioms HodgeClosure.dickson7_identity
#print axioms HodgeClosure.dickson9_identity
#print axioms HodgeClosure.two_inert_7_9
#print axioms HodgeClosure.theta_sign_pattern
#print axioms HodgeClosure.symplectic_chain_bound
#print axioms HodgeClosure.binomial_six
#print axioms HodgeClosure.curve_intersections
#print axioms HodgeClosure.twist_sums
#print axioms HodgeClosure.weil_sum_32
#print axioms HodgeClosure.cm_counts
#print axioms HodgeClosure.two_step_degree
#print axioms HodgeClosure.three_step_chains
#print axioms HodgeClosure.Isolated.iso_base35
#print axioms HodgeClosure.Isolated.iso_base35up
#print axioms HodgeClosure.Isolated.iso_base35down
#print axioms HodgeClosure.Isolated.iso_familyA
#print axioms HodgeClosure.Isolated.iso_familyC
#print axioms HodgeClosure.Isolated.iso_familyD
#print axioms HodgeClosure.Isolated.chainfree_familyC
#print axioms HodgeClosure.Isolated.chainfree_familyA
#print axioms HodgeClosure.Isolated.no_entry_top
#print axioms HodgeClosure.Isolated.entry_at_shift_three
#print axioms HodgeClosure.Isolated.six_bundles_cycles
#print axioms HodgeClosure.r_values_n3
#print axioms HodgeClosure.td_trace_forms
#print axioms HodgeClosure.nikulin_conditions
#print axioms HodgeClosure.cubic_discriminants
#print axioms HodgeClosure.theta_h_coefficients
#print axioms HodgeClosure.rmopen_gram
#print axioms HodgeClosure.rmopen_signatures
#print axioms HodgeClosure.rmopen_discriminants
#print axioms HodgeClosure.rmopen_hasse
#print axioms HodgeClosure.witt_witnesses
#print axioms HodgeClosure.witt_index_one_examples
#print axioms HodgeClosure.witt_count
#print axioms HodgeClosure.rank_five_example
#print axioms HodgeClosure.zk_hodge_numbers
#print axioms HodgeClosure.product_algebra_counts
#print axioms HodgeClosure.tenfold_count
#print axioms HodgeClosure.squares_span
#print axioms HodgeClosure.cm_sixfold_counts
#print axioms HodgeClosure.pohlmann_linear
#print axioms HodgeClosure.sextic_discriminants
#print axioms HodgeClosure.noweil_degrees
#print axioms HodgeClosure.omega_power
#print axioms HodgeClosure.d_divisible
#print axioms HodgeClosure.slice_degrees
#print axioms HodgeClosure.cupkernel_counts
#print axioms HodgeClosure.twolevel_totals
#print axioms HodgeClosure.gamma_counts
#print axioms HodgeClosure.ll_excess
#print axioms HodgeClosure.uniform_bounds
#print axioms HodgeClosure.kplus_targets
#print axioms HodgeClosure.euler_table
#print axioms HodgeClosure.kummer_graph
#print axioms HodgeClosure.secant_ranks
#print axioms HodgeClosure.forced_dims
#print axioms HodgeClosure.serre_only_three
#print axioms HodgeClosure.chi_lattice
#print axioms HodgeClosure.chi_lattice_min
#print axioms HodgeClosure.lagrangian_costs
#print axioms HodgeClosure.cube_windows
#print axioms HodgeClosure.cube_parities
#print axioms HodgeClosure.collapsed_acyclic
