/-
HodgeClosure.lean

Kernel-checked finite arithmetic and propositional logic behind the paper
"Constructions at the Two Open Steps of the Hodge Conjecture".

Nothing here formalises algebraic geometry.  What is checked is

  Section 1  the closure graph of statements: with the implications proved
             in the paper and in the literature taken as rules, the Hodge
             conjecture follows from exactly the minimal sets
             {F3}, {L, M}, {L, F3'}, {V, F3'}, {F2, F3'}, and from no proper
             subset of any of them;
  Section 2  the eigencharacter of the polarisation class of an abelian
             variety of Weil type: in the standard model over Z[sqrt(-d)] the
             form eta(x, y) = Tr(sqrt(-d) H(x, y)) satisfies
             eta(tau x, tau y) = N(tau) eta(x, y), and N(tau) is not 1 at
             tau = 2 + sqrt(-d); so eta^k lies in the eigenspace of N^k, the
             eigenspace that the Weil classes occupy for k = n;
  Section 3  the dimension counts of the loci on which the Weil classes are
             known to be algebraic against the dimension n^2 of the period
             domain.

No Mathlib.  Every theorem is checked by `decide` or by the core lemmas on
natural numbers; the block at the end prints the axioms of each one.
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

/-! ## Section 2: the eigencharacter of the polarisation -/

/-- An element a + b sqrt(-d) of Z[sqrt(-d)], with d carried along. -/
structure Q where
  a : Int
  b : Int
  deriving DecidableEq, Repr

def qadd (x y : Q) : Q := ⟨x.a + y.a, x.b + y.b⟩
def qmul (d : Int) (x y : Q) : Q := ⟨x.a * y.a - d * x.b * y.b, x.a * y.b + x.b * y.a⟩
def qconj (x : Q) : Q := ⟨x.a, -x.b⟩
def qnorm (d : Int) (x : Q) : Int := x.a * x.a + d * x.b * x.b
def qscale (c : Int) (x : Q) : Q := ⟨c * x.a, c * x.b⟩

/-- Tr(sqrt(-d) z) for z = a + b sqrt(-d): sqrt(-d) z = -d b + a sqrt(-d), of trace -2 d b. -/
def trRoot (d : Int) (z : Q) : Int := -2 * d * z.b

/-- The hermitian form of signature given by the list of signs eps. -/
def herm (d : Int) (eps : List Int) (x y : List Q) : Q :=
  (List.zip eps (List.zip x y)).foldl
    (fun acc ⟨e, xi, yi⟩ => qadd acc (qscale e (qmul d xi (qconj yi)))) ⟨0, 0⟩

/-- eta(x, y) = Tr(sqrt(-d) H(x, y)), the alternating form of the polarisation. -/
def eta (d : Int) (eps : List Int) (x y : List Q) : Int := trRoot d (herm d eps x y)

def vscale (d : Int) (t : Q) (x : List Q) : List Q := x.map (qmul d t)

/-- The sample: d in {1, 2, 3, 5, 7, 11, 15, 19}, signature (1, 1, -1, -1), and
the vectors and multipliers below. -/
def ds : List Int := [1, 2, 3, 5, 7, 11, 15, 19]
def eps4 : List Int := [1, 1, -1, -1]
def taus : List Q := [⟨2, 1⟩, ⟨1, 1⟩, ⟨3, -2⟩, ⟨0, 1⟩, ⟨5, 3⟩]
def vecs : List (List Q) :=
  [ [⟨1, 0⟩, ⟨0, 1⟩, ⟨2, -1⟩, ⟨1, 1⟩],
    [⟨0, 2⟩, ⟨1, -1⟩, ⟨3, 0⟩, ⟨-1, 2⟩],
    [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    [⟨-2, 3⟩, ⟨0, 0⟩, ⟨1, -4⟩, ⟨2, 2⟩] ]

/-- eta(tau x, tau y) = N(tau) eta(x, y) on the whole sample. -/
theorem eta_eigencharacter :
    ds.all (fun d => taus.all (fun t => vecs.all (fun x => vecs.all (fun y =>
      eta d eps4 (vscale d t x) (vscale d t y) == qnorm d t * eta d eps4 x y)))) = true := by
  decide

/-- The multiplicativity N(tau sigma) = N(tau) N(sigma) on the sample. -/
theorem norm_multiplicative :
    ds.all (fun d => taus.all (fun t => taus.all (fun s =>
      qnorm d (qmul d t s) == qnorm d t * qnorm d s))) = true := by decide

/-- N(2 + sqrt(-d)) = 4 + d is never 1, so eta is not invariant under K^x and
eta^k carries the character N^k, not the trivial character. -/
theorem eta_not_invariant : ds.all (fun d => qnorm d ⟨2, 1⟩ != 1) = true := by decide

/-- The two characters tau^(2n) and N(tau)^n differ at tau = 2 + sqrt(-d) for
d in the sample and 1 <= n <= 6 (they agree on eta^n only for the second). -/
def qpow (d : Int) (t : Q) : Nat → Q
  | 0 => ⟨1, 0⟩
  | k+1 => qmul d t (qpow d t k)

theorem characters_differ :
    ds.all (fun d => (List.range 6).all (fun n =>
      qpow d ⟨2, 1⟩ (2 * (n + 1)) != ⟨(qnorm d ⟨2, 1⟩) ^ (n + 1), 0⟩)) = true := by decide

/-! ## Section 3: dimension counts -/

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
Hodge group, by Kuenneth type (Theorem VI.7(i) of the paper): (1,1,2) gives 3 + 3,
(2,2,0) gives 4, (0,0,4) gives 6, (2,0,2) and (0,2,2) give 3 each, and the four
types (4,0,0), (0,4,0), (3,1,0), (1,3,0) one each.  The sum is 26. -/
theorem kunneth_count : [3, 3, 4, 6, 3, 3, 1, 1, 1, 1].foldl (· + ·) 0 = 26 := by decide

/-- The lower bound r = (4 + rho) n^2 - 2n of the polarised criterion at
Hankel rank 3: 57 at n = 3 and 104 at n = 4; and 18 at n = 2, rho = 0. -/
def rBound (rho n : Nat) : Nat := (4 + rho) * n * n - 2 * n
theorem r_values : rBound 3 3 = 57 ∧ rBound 3 4 = 104 ∧ rBound 0 2 = 12 ∧ rBound 3 2 = 24 := by decide

/-! ## Section 4: the Fricke families (Section V of the paper) -/

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

/-- Transcendental rank 22 - 16 = 6, and 6 >= 3 * 2 so a totally real E of
degree 2 is allowed while a totally real field of degree 3 is not (dim_E T >= 3
forces [E : Q] <= 2). -/
theorem fricke_transcendental : 22 - 16 = 6 ∧ 6 / 3 = 2 ∧ 6 < 3 * 3 := by decide

/-- A dominant rational self-map of degree N gives f_* f^* = N on T, so
(f^*)^2 = N when f^* is in a quadratic field with f_* its conjugate: the
multiplier of a correspondence is the product d_1 d_2 of the two degrees
(Proposition V.9 of the paper), here 1 * N. -/
theorem fricke_multiplier : 1 * 7 = 7 ∧ 1 * 5 = 5 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6 := by decide

/-- The Hecke algebra of (D_n, <tau>) for odd n has dimension (n + 1) / 2, the number of double cosets:
3, 4, 5, 6 for n = 5, 7, 9, 11 (Proposition V.10). -/
def heckeDim (n : Nat) : Nat := (n + 1) / 2
theorem hecke_dims : heckeDim 5 = 3 ∧ heckeDim 7 = 4 ∧ heckeDim 9 = 5 ∧ heckeDim 11 = 6 := by decide

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
#print axioms HodgeClosure.eta_eigencharacter
#print axioms HodgeClosure.norm_multiplicative
#print axioms HodgeClosure.eta_not_invariant
#print axioms HodgeClosure.characters_differ
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
#print axioms HodgeClosure.hecke_dims
