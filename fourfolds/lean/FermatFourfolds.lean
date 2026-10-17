/-
FermatFourfolds.lean

Kernel-checked finite arithmetic behind the paper
"The Hodge conjecture for Fermat fourfolds of degree not divisible by 6 or 110".

Nothing here formalises algebraic geometry. A multiset of residues modulo M
is a list of natural numbers; it is balanced when its sum is 0 modulo M, no
entry is 0 modulo M, and for every unit t the representatives of t*a add up
to (number of entries) * M / 2.

No Mathlib. Every theorem is a finite computation checked by the kernel
(`decide +kernel`); the block at the end prints the axioms of each one, and
none uses any axiom.
-/

set_option maxRecDepth 100000

namespace FermatFourfolds

/-! ## Basic notions -/

/-- `h t` for the multiset `A` at level `M`: the sum of the representatives
of `t * a` in `0, ..., M - 1`. -/
def hsum (M t : Nat) (A : List Nat) : Nat := (A.map (fun a => t * a % M)).sum

/-- The balancing condition of the paper, as a Boolean. -/
def balanced (M : Nat) (A : List Nat) : Bool :=
  (A.sum % M == 0) && A.all (fun a => a % M != 0) &&
  (List.range M).all (fun t => Nat.gcd t M != 1 || hsum M t A * 2 == A.length * M)

/-- The additive order of `y` modulo `M`. -/
def ord (M y : Nat) : Nat := M / Nat.gcd y M

/-- The representative of `-y` modulo `M`. -/
def neg (M y : Nat) : Nat := (M - y % M) % M

/-- The multiset `t * A`, entry by entry. -/
def mul (M t : Nat) (A : List Nat) : List Nat := A.map (fun a => t * a % M)

/-- Equality of multisets of residues modulo `M`. -/
def msEq (M : Nat) (A B : List Nat) : Bool :=
  let A' := A.map (· % M)
  let B' := B.map (· % M)
  A'.length == B'.length && A'.all (fun a => A'.count a == B'.count a)

/-- No two entries of the multiset add up to `0` modulo `M`. -/
def noPair (M : Nat) : List Nat → Bool
  | [] => true
  | a :: rest => rest.all (fun b => (a + b) % M != 0) && noPair M rest

/-- Remove the elements of `S` from `A`, with multiplicity. -/
def removeAll (A S : List Nat) : List Nat := S.foldl List.erase A

/-- The move `(T, S)` applied to `A`: `S` is replaced by `-(T - S)`. -/
def move (M : Nat) (A T S : List Nat) : List Nat :=
  removeAll A S ++ (removeAll T S).map (neg M)

def isPrime (p : Nat) : Bool :=
  Nat.ble 2 p && (List.range p).all (fun d => Nat.blt d 2 || p % d != 0)

/-- The odd primes dividing `M`. -/
def oddPrimes (M : Nat) : List Nat :=
  (List.range (M + 1)).filter (fun l => l % 2 == 1 && isPrime l && M % l == 0)

/-! ## The standard multisets (Section 2) -/

/-- The coset `Phi_l(x) = {x + j M / l : 0 <= j < l}`. -/
def phi (M l x : Nat) : List Nat := (List.range l).map (fun j => (x + j * (M / l)) % M)

/-- `sigma_{l,x} = Phi_l(x) + {-l x}`. -/
def sigma (M l x : Nat) : List Nat := phi M l x ++ [neg M (l * x)]

/-- `T(x) = {x, x + M/2, -2x, M/2}`. -/
def tee (M x : Nat) : List Nat := [x % M, (x + M / 2) % M, neg M (2 * x), M / 2]

/-- The pair `{y, -y}`. -/
def pair (M y : Nat) : List Nat := [y % M, neg M y]

/-- The pairs and the standard multisets at level `M`, which generate `S_M`. -/
def gensS (M : Nat) : List (List Nat) :=
  ((List.range M).filter (· != 0)).map (pair M) ++
  (oddPrimes M).flatMap (fun l =>
    ((List.range M).filter (fun x => l * x % M != 0)).map (sigma M l)) ++
  (if M % 2 == 0 then ((List.range M).filter (fun x => 2 * x % M != 0)).map (tee M)
   else [])

/-- The number of entries of `A` counted by `nu` is even for every generator
of `S_M`, so the homomorphism `nu` vanishes on `S_M`. -/
def vanishesOnS (M : Nat) (nu : Nat → Bool) : Bool :=
  (gensS M).all (fun A => (A.filter nu).length % 2 == 0)

/-- The parity of the number of entries counted by `nu`. -/
def nuOf (nu : Nat → Bool) (A : List Nat) : Nat := (A.filter nu).length % 2

theorem standard_examples :
    tee 28 3 = [3, 17, 22, 14] ∧ phi 20 5 1 = [1, 5, 9, 13, 17] ∧
    neg 20 5 = 15 := by decide +kernel

/-- The lowering move of the figure at level `28`. -/
theorem move_example :
    balanced 28 [3, 5, 13, 17, 19, 27] = true ∧
    msEq 28 (move 28 [3, 5, 13, 17, 19, 27] (tee 28 3) [3, 17])
      [5, 6, 13, 14, 19, 27] = true ∧
    balanced 28 [5, 6, 13, 14, 19, 27] = true ∧
    ord 28 3 = 28 ∧ ord 28 17 = 28 ∧ ord 28 6 = 14 ∧ ord 28 14 = 2 := by
  decide +kernel

/-- At the levels used in the paper the standard multisets are balanced. -/
theorem standard_balanced :
    (gensS 21).all (balanced 21) = true ∧ (gensS 28).all (balanced 28) = true ∧
    (gensS 33).all (balanced 33) = true ∧ (gensS 35).all (balanced 35) = true ∧
    (gensS 39).all (balanced 39) = true ∧ (gensS 44).all (balanced 44) = true ∧
    (gensS 52).all (balanced 52) = true ∧ (gensS 66).all (balanced 66) = true ∧
    (gensS 78).all (balanced 78) = true := by decide +kernel

theorem standard_balanced_large :
    (gensS 102).all (balanced 102) = true ∧ (gensS 110).all (balanced 110) = true ∧
    (gensS 114).all (balanced 114) = true := by decide +kernel

/-! ## Section 4: the exceptional orbits -/

def O21 : List Nat := [1, 4, 9, 15, 16, 18]
def O33 : List Nat := [1, 4, 16, 22, 25, 31]
def O39 : List Nat := [1, 7, 16, 22, 34, 37]

/-- The description of the three sets by residues. -/
theorem orbits_by_residues :
    msEq 21 O21 ((List.range 21).filter (fun x => x % 3 == 1 && [1, 2, 4].contains (x % 7))
      ++ [3, 5, 6].map (3 * ·)) = true ∧
    msEq 33 O33 ((List.range 33).filter
      (fun x => x % 3 == 1 && [1, 3, 4, 5, 9].contains (x % 11)) ++ [22]) = true ∧
    msEq 39 O39 ((List.range 39).filter
      (fun x => x % 3 == 1 && [1, 3, 9, 7, 8, 11].contains (x % 13))) = true := by
  decide +kernel

/-- `t O = O` for the units named in the proof, and the cosets of the group
they generate with `-1` are represented by `1, 2`, by `1, 5` and by
`1, 2, 4, 8`. -/
theorem orbits_cosets :
    ((List.range 21).filter (fun t => Nat.gcd t 21 == 1 && t % 3 == 1 &&
        [1, 2, 4].contains (t % 7))).all (fun t => msEq 21 (mul 21 t O21) O21) = true ∧
    ((List.range 33).filter (fun t => Nat.gcd t 33 == 1 && t % 3 == 1 &&
        [1, 3, 4, 5, 9].contains (t % 11))).all (fun t => msEq 33 (mul 33 t O33) O33) = true ∧
    ((List.range 39).filter (fun t => Nat.gcd t 39 == 1 && t % 3 == 1 &&
        [1, 3, 9].contains (t % 13))).all (fun t => msEq 39 (mul 39 t O39) O39) = true ∧
    ((List.range 21).filter (fun t => Nat.gcd t 21 == 1)).all (fun t =>
      [1, 2].any (fun s => msEq 21 (mul 21 t O21) (mul 21 s O21) ||
        msEq 21 (mul 21 t O21) ((mul 21 s O21).map (neg 21)))) = true ∧
    ((List.range 33).filter (fun t => Nat.gcd t 33 == 1)).all (fun t =>
      [1, 5].any (fun s => msEq 33 (mul 33 t O33) (mul 33 s O33) ||
        msEq 33 (mul 33 t O33) ((mul 33 s O33).map (neg 33)))) = true ∧
    ((List.range 39).filter (fun t => Nat.gcd t 39 == 1)).all (fun t =>
      [1, 2, 4, 8].any (fun s => msEq 39 (mul 39 t O39) (mul 39 s O39) ||
        msEq 39 (mul 39 t O39) ((mul 39 s O39).map (neg 39)))) = true := by
  decide +kernel

theorem orbits_balanced :
    mul 21 2 O21 = [2, 8, 18, 9, 11, 15] ∧ mul 33 5 O33 = [5, 20, 14, 11, 26, 23] ∧
    mul 39 2 O39 = [2, 14, 32, 5, 29, 35] ∧ mul 39 4 O39 = [4, 28, 25, 10, 19, 31] ∧
    mul 39 8 O39 = [8, 17, 11, 20, 38, 23] ∧
    (mul 21 2 O21).sum = 63 ∧ (mul 33 5 O33).sum = 99 ∧ (mul 39 2 O39).sum = 117 ∧
    (mul 39 4 O39).sum = 117 ∧ (mul 39 8 O39).sum = 117 ∧
    O21.sum = 63 ∧ O33.sum = 99 ∧ O39.sum = 117 ∧
    balanced 21 O21 = true ∧ balanced 33 O33 = true ∧ balanced 39 O39 = true := by
  decide +kernel

/-- The identities of the proof of algebraicity. -/
theorem orbits_identities :
    sigma 21 3 2 = [2, 9, 16, 15] ∧
    msEq 21 (O21 ++ [2, 19]) (sigma 21 3 2 ++ [1, 4, 18, 19]) = true ∧
    balanced 21 [1, 4, 18, 19] = true ∧
    mul 66 2 O33 = [2, 8, 32, 44, 50, 62] ∧
    msEq 66 [2, 32, 33, 65] (tee 66 32) = true ∧ msEq 66 [8, 33, 41, 50] (tee 66 8) = true ∧
    msEq 66 ([2, 8, 32, 44, 50, 62] ++ [1, 65] ++ [25, 41] ++ [33, 33])
      ([1, 25, 44, 62] ++ tee 66 32 ++ tee 66 8) = true ∧
    balanced 66 [1, 25, 44, 62] = true ∧ balanced 66 [2, 8, 32, 44, 50, 62] = true ∧
    mul 78 2 O39 = [2, 14, 32, 44, 68, 74] ∧
    msEq 78 [14, 32, 39, 71] (tee 78 32) = true ∧ msEq 78 [5, 39, 44, 68] (tee 78 5) = true ∧
    msEq 78 ([2, 14, 32, 44, 68, 74] ++ [5, 73] ++ [7, 71] ++ [39, 39])
      ([2, 7, 73, 74] ++ tee 78 32 ++ tee 78 5) = true ∧
    balanced 78 [2, 7, 73, 74] = true ∧ balanced 78 [2, 14, 32, 44, 68, 74] = true := by
  decide +kernel

/-- Small facts used in the case analysis of Section 4. -/
theorem odd_case_facts :
    -- three-element subsets of {1,...,6} with sum divisible by 7
    ((List.range 7).flatMap (fun a => (List.range 7).flatMap (fun b =>
      (List.range 7).filterMap (fun c =>
        if 0 < a && a < b && b < c && (a + b + c) % 7 == 0 then some [a, b, c] else none))))
      = [[1, 2, 4], [3, 5, 6]] ∧
    -- the cosets C_j = 2^j <3> in (Z/13)^x, with -C_j = C_{j+2}
    mul 13 1 [1, 3, 9] = [1, 3, 9] ∧ mul 13 2 [1, 3, 9] = [2, 6, 5] ∧
    mul 13 4 [1, 3, 9] = [4, 12, 10] ∧ mul 13 8 [1, 3, 9] = [8, 11, 7] ∧
    msEq 13 ([1, 3, 9].map (neg 13)) [4, 12, 10] = true ∧
    msEq 13 ([2, 6, 5].map (neg 13)) [8, 11, 7] = true ∧
    -- 3 and 5 are nonsquares modulo 7, 3 generates (Z/7)^x, and the
    -- subgroup generated by 3 modulo 11 is the group of nonzero squares
    ((List.range 7).filter (fun x => 0 < x)).map (fun x => x * x % 7) = [1, 4, 2, 2, 4, 1] ∧
    (List.range 6).map (fun j => 3 ^ j % 7) = [1, 3, 2, 6, 4, 5] ∧
    (List.range 5).map (fun j => 3 ^ j % 11) = [1, 3, 9, 5, 4] ∧
    ((List.range 11).filter (fun x => 0 < x)).map (fun x => x * x % 11)
      = [1, 4, 9, 5, 3, 3, 5, 9, 4, 1] := by
  decide +kernel

/-! ## Section 5: Aoki's sets Q(M) and the parity invariants -/

def val2 : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, q => if q % 2 == 0 && 0 < q then 1 + val2 fuel (q / 2) else 0

/-- `q` is a product of an even number of distinct elements of `{4, 3, 5, 7, 11, ...}`. -/
def evenProduct (q : Nat) : Bool :=
  let a := val2 q q
  let o := q / 2 ^ a
  (a == 0 || a == 2) &&
  (oddPrimes o).all (fun l => o % (l * l) != 0) &&
  ((if a == 2 then 1 else 0) + (oddPrimes o).length) % 2 == 0

/-- The set `Q(M)`. -/
def Qset (M : Nat) : List Nat :=
  (List.range (M + 1)).filter (fun q => 1 < q && M % q == 0 && evenProduct q)

theorem aoki_sets :
    Qset 114 = [57] ∧ Qset 102 = [51] ∧ Qset 44 = [44] ∧ Qset 52 = [52] ∧
    Qset 33 = [33] ∧ Qset 35 = [35] ∧ Qset 39 = [39] ∧ Qset 110 = [55] ∧
    Qset 1680 = [12, 15, 20, 21, 28, 35, 420] := by decide +kernel

/-- The homomorphisms of Corollary `cor:Bone` vanish on the generators of
`S_M` at the levels where they are used. -/
theorem parity_invariants :
    vanishesOnS 114 (fun y => ord 114 y == 19) = true ∧
    vanishesOnS 102 (fun y => ord 102 y == 17) = true ∧
    vanishesOnS 44 (fun y => ord 44 y == 11) = true ∧
    vanishesOnS 52 (fun y => ord 52 y == 13) = true ∧
    vanishesOnS 33 (fun y => y * y % 33 == 1) = true ∧
    vanishesOnS 35 (fun y => y * y % 35 == 1) = true ∧
    vanishesOnS 39 (fun y => y * y % 39 == 1) = true := by decide +kernel

/-! ## Section 6: five pairs of characters and their block patterns -/

/-- `<t a>` for a character `a`: the sum of the representatives of `t a`,
divided by the level. -/
def angle (m t : Nat) (a : List Nat) : Nat := hsum m t a / m

/-- `a` is a character: nonzero entries with sum divisible by `m`. -/
def isChar (m : Nat) (a : List Nat) : Bool := a.all (fun x => x % m != 0) && a.sum % m == 0

/-- `<t a> + <t b> = s` for every unit `t`. -/
def joinSum (m : Nat) (a b : List Nat) (s : Nat) : Bool :=
  (List.range m).all (fun t => Nat.gcd t m != 1 ||
    (hsum m t a % m == 0 && hsum m t b % m == 0 && angle m t a + angle m t b == s))

/-- The units below `m / 2`. -/
def halfUnits (m : Nat) : List Nat :=
  (List.range m).filter (fun t => Nat.gcd t m == 1 && 2 * t < m)

def angles (m : Nat) (a : List Nat) : List Nat := (halfUnits m).map (fun t => angle m t a)

theorem charpair_114 :
    isChar 114 [1, 25, 43, 57, 102] = true ∧ isChar 114 [39, 63, 68, 80, 92] = true ∧
    [1, 25, 43, 57, 102].sum = 228 ∧ [39, 63, 68, 80, 92].sum = 342 ∧
    joinSum 114 [1, 25, 43, 57, 102] [39, 63, 68, 80, 92] 5 = true ∧
    halfUnits 114 = [1, 5, 7, 11, 13, 17, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55] ∧
    angles 114 [1, 25, 43, 57, 102] = [2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 2] ∧
    angles 114 [39, 63, 68, 80, 92] = [3, 3, 3, 3, 2, 3, 3, 3, 2, 2, 3, 3, 2, 3, 3, 2, 2, 3] ∧
    msEq 114 ([1, 25, 43, 57, 102] ++ [39, 63, 68, 80, 92])
      [1, 25, 39, 43, 57, 63, 68, 80, 92, 102] = true ∧
    balanced 114 [1, 25, 39, 43, 57, 63, 68, 80, 92, 102] = true ∧
    noPair 114 [1, 25, 39, 43, 57, 63, 68, 80, 92, 102] = true ∧
    (List.range 114).filter (fun y => ord 114 y == 19) =
      (List.range 19).filterMap (fun j => if 0 < j then some (6 * j) else none) ∧
    [1, 25, 39, 43, 57, 63, 68, 80, 92, 102].filter (fun y => ord 114 y == 19) = [102] := by
  decide +kernel

theorem charpair_44 :
    isChar 44 [1, 5, 8, 33, 41] = true ∧ isChar 44 [9, 37, 42] = true ∧
    [1, 5, 8, 33, 41].sum = 88 ∧ [9, 37, 42].sum = 88 ∧
    joinSum 44 [1, 5, 8, 33, 41] [9, 37, 42] 4 = true ∧
    halfUnits 44 = [1, 3, 5, 7, 9, 13, 15, 17, 19, 21] ∧
    angles 44 [1, 5, 8, 33, 41] = [2, 2, 3, 2, 2, 2, 3, 3, 2, 3] ∧
    angles 44 [9, 37, 42] = [2, 2, 1, 2, 2, 2, 1, 1, 2, 1] ∧
    msEq 44 ([1, 5, 8, 33, 41] ++ [9, 37, 42]) [1, 5, 8, 9, 33, 37, 41, 42] = true ∧
    balanced 44 [1, 5, 8, 9, 33, 37, 41, 42] = true ∧
    noPair 44 [1, 5, 8, 9, 33, 37, 41, 42] = true ∧
    (List.range 44).filter (fun y => ord 44 y == 11) =
      (List.range 11).filterMap (fun j => if 0 < j then some (4 * j) else none) ∧
    [1, 5, 8, 9, 33, 37, 41, 42].filter (fun y => ord 44 y == 11) = [8] := by
  decide +kernel

theorem charpair_52 :
    isChar 52 [1, 5, 16, 37, 45] = true ∧ isChar 52 [29, 18, 42, 50, 17] = true ∧
    [1, 5, 16, 37, 45].sum = 104 ∧ [29, 18, 42, 50, 17].sum = 156 ∧
    joinSum 52 [1, 5, 16, 37, 45] [29, 18, 42, 50, 17] 5 = true ∧
    halfUnits 52 = [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25] ∧
    angles 52 [1, 5, 16, 37, 45] = [2, 2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 3] ∧
    angles 52 [29, 18, 42, 50, 17] = [3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2] ∧
    msEq 52 ([1, 5, 16, 37, 45] ++ [29, 18, 42, 50, 17])
      [1, 5, 16, 17, 18, 29, 37, 42, 45, 50] = true ∧
    balanced 52 [1, 5, 16, 17, 18, 29, 37, 42, 45, 50] = true ∧
    noPair 52 [1, 5, 16, 17, 18, 29, 37, 42, 45, 50] = true ∧
    (List.range 52).filter (fun y => ord 52 y == 13) =
      (List.range 13).filterMap (fun j => if 0 < j then some (4 * j) else none) ∧
    [1, 5, 16, 17, 18, 29, 37, 42, 45, 50].filter (fun y => ord 52 y == 13) = [16] := by
  decide +kernel

theorem charpair_102 :
    isChar 102 [1, 7, 51, 60, 85] = true ∧ isChar 102 [91, 34, 26, 98, 57] = true ∧
    [1, 7, 51, 60, 85].sum = 204 ∧ [91, 34, 26, 98, 57].sum = 306 ∧
    joinSum 102 [1, 7, 51, 60, 85] [91, 34, 26, 98, 57] 5 = true ∧
    halfUnits 102 = [1, 5, 7, 11, 13, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49] ∧
    angles 102 [1, 7, 51, 60, 85] = [2, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2, 3, 2, 3, 2, 3] ∧
    angles 102 [91, 34, 26, 98, 57] = [3, 3, 3, 3, 2, 3, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2] ∧
    msEq 102 ([1, 7, 51, 60, 85] ++ [91, 34, 26, 98, 57])
      [1, 7, 26, 34, 51, 57, 60, 85, 91, 98] = true ∧
    balanced 102 [1, 7, 26, 34, 51, 57, 60, 85, 91, 98] = true ∧
    noPair 102 [1, 7, 26, 34, 51, 57, 60, 85, 91, 98] = true ∧
    (List.range 102).filter (fun y => ord 102 y == 17) =
      (List.range 17).filterMap (fun j => if 0 < j then some (6 * j) else none) ∧
    [1, 7, 26, 34, 51, 57, 60, 85, 91, 98].filter (fun y => ord 102 y == 17) = [60] := by
  decide +kernel

theorem charpair_35 :
    isChar 35 [1, 2, 16, 21, 30] = true ∧ isChar 35 [17, 22, 31] = true ∧
    [1, 2, 16, 21, 30].sum = 70 ∧ [17, 22, 31].sum = 70 ∧
    joinSum 35 [1, 2, 16, 21, 30] [17, 22, 31] 4 = true ∧
    halfUnits 35 = [1, 2, 3, 4, 6, 8, 9, 11, 12, 13, 16, 17] ∧
    angles 35 [1, 2, 16, 21, 30] = [2, 2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 3] ∧
    angles 35 [17, 22, 31] = [2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1] ∧
    mul 35 8 [1, 2, 16, 21, 30] = [8, 16, 23, 28, 30] ∧ [8, 16, 23, 28, 30].sum = 105 ∧
    mul 35 8 [17, 22, 31] = [31, 1, 3] ∧ [31, 1, 3].sum = 35 ∧
    msEq 35 ([1, 2, 16, 21, 30] ++ [17, 22, 31]) [1, 2, 16, 17, 21, 22, 30, 31] = true ∧
    balanced 35 [1, 2, 16, 17, 21, 22, 30, 31] = true ∧
    noPair 35 [1, 2, 16, 17, 21, 22, 30, 31] = true ∧
    (List.range 35).filter (fun y => y * y % 35 == 1) = [1, 6, 29, 34] ∧
    [1, 2, 16, 17, 21, 22, 30, 31].filter (fun y => y * y % 35 == 1) = [1] := by
  decide +kernel

/-- The `k`-th entry of a list, `0` past its end. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: r, n + 1 => nth r n

/-- `g . a` for an integer vector `g` and the representatives `a`. -/
def dot (e a : List Nat) : Nat := (List.zipWith (· * ·) e a).sum

/-- The `k`-th coordinate of `sum_l delta_l e_l`. -/
def colSum (cols : List (List Nat × Nat)) (k : Nat) : Nat :=
  (cols.map (fun c => nth c.1 k * c.2)).sum

/-- Conditions (P1), (P2), (P3) of a block pattern for a character with five
entries. -/
def blockPattern (m : Nat) (a : List Nat) (D : Nat) (cols : List (List Nat × Nat)) : Bool :=
  a.length == 5 && isChar m a &&
  (List.range 5).all (fun k => colSum cols k == D) &&
  cols.all (fun c => c.1.length == 5 && c.1.any (0 < ·) && c.1.any (· == 0) &&
    dot c.1 a % m == 0 && 0 < c.2) &&
  Nat.blt D (cols.map (·.2)).sum

def weights (a : List Nat) (cols : List (List Nat × Nat)) : List Nat :=
  cols.map (fun c => dot c.1 a)

def degSum (cols : List (List Nat × Nat)) : Nat := (cols.map (·.2)).sum

def pat114a : List (List Nat × Nat) :=
  [([0, 0, 1, 2, 0], 1), ([0, 0, 2, 0, 1], 1), ([1, 3, 0, 0, 0], 1), ([2, 0, 0, 1, 2], 1)]
def pat114b : List (List Nat × Nat) :=
  [([3, 1, 2, 0, 0], 7), ([0, 1, 5, 0, 1], 2), ([0, 0, 0, 2, 0], 12), ([1, 5, 0, 0, 1], 3),
   ([0, 0, 0, 0, 19], 1)]
def pat44 : List (List Nat × Nat) :=
  [([3, 0, 0, 0, 1], 1), ([0, 0, 11, 0, 0], 1), ([1, 1, 0, 0, 2], 5), ([1, 2, 0, 1, 0], 3),
   ([0, 0, 0, 4, 0], 2)]
def pat52a : List (List Nat × Nat) :=
  [([0, 0, 0, 3, 1], 4), ([0, 1, 1, 0, 3], 1), ([2, 1, 0, 0, 1], 7), ([0, 0, 13, 0, 0], 1),
   ([0, 3, 0, 1, 0], 2)]
def pat52b : List (List Nat × Nat) :=
  [([0, 0, 5, 1, 0], 1), ([3, 0, 0, 0, 1], 1), ([2, 0, 0, 3, 0], 1), ([0, 3, 0, 1, 0], 1),
   ([0, 1, 0, 0, 2], 2)]
def pat102a : List (List Nat × Nat) :=
  [([0, 0, 0, 3, 2], 1), ([0, 0, 3, 0, 4], 1), ([0, 3, 0, 0, 0], 2), ([2, 0, 1, 1, 0], 3)]
def pat102b : List (List Nat × Nat) :=
  [([0, 0, 0, 0, 6], 2), ([0, 0, 0, 17, 0], 1), ([0, 0, 2, 0, 0], 9), ([0, 6, 0, 1, 0], 1),
   ([3, 2, 0, 0, 1], 6)]
def pat35 : List (List Nat × Nat) :=
  [([0, 0, 0, 5, 0], 10), ([1, 1, 2, 0, 0], 25), ([1, 2, 0, 0, 1], 10), ([3, 1, 0, 0, 1], 5),
   ([0, 0, 0, 0, 35], 1)]

/-- The table of Corollary `cor:patterns`: the characters, the block patterns,
the weights and the degree sums. -/
theorem block_patterns :
    Nat.gcd 13 114 = 1 ∧ mul 114 13 [39, 63, 68, 80, 92] = [51, 21, 86, 14, 56] ∧
    blockPattern 114 [51, 21, 86, 14, 56] 3 pat114a = true ∧
    weights [51, 21, 86, 14, 56] pat114a = [114, 228, 114, 228] ∧ degSum pat114a = 4 ∧
    blockPattern 114 [1, 25, 43, 57, 102] 24 pat114b = true ∧
    weights [1, 25, 43, 57, 102] pat114b = [114, 342, 114, 228, 1938] ∧
    degSum pat114b = 25 ∧
    blockPattern 44 [1, 5, 8, 33, 41] 11 pat44 = true ∧
    weights [1, 5, 8, 33, 41] pat44 = [44, 88, 88, 44, 132] ∧ degSum pat44 = 12 ∧
    blockPattern 52 [1, 5, 16, 37, 45] 14 pat52a = true ∧
    weights [1, 5, 16, 37, 45] pat52a = [156, 156, 52, 208, 52] ∧ degSum pat52a = 15 ∧
    Nat.gcd 9 52 = 1 ∧ mul 52 9 [29, 18, 42, 50, 17] = [1, 6, 14, 34, 49] ∧
    blockPattern 52 [1, 6, 14, 34, 49] 5 pat52b = true ∧
    weights [1, 6, 14, 34, 49] pat52b = [104, 52, 104, 52, 104] ∧ degSum pat52b = 6 ∧
    Nat.gcd 37 102 = 1 ∧ mul 102 37 [91, 34, 26, 98, 57] = [1, 34, 44, 56, 69] ∧
    blockPattern 102 [1, 34, 44, 56, 69] 6 pat102a = true ∧
    weights [1, 34, 44, 56, 69] pat102a = [306, 408, 102, 102] ∧ degSum pat102a = 7 ∧
    Nat.gcd 5 102 = 1 ∧ mul 102 5 [1, 7, 51, 60, 85] = [5, 35, 51, 96, 17] ∧
    blockPattern 102 [5, 35, 51, 96, 17] 18 pat102b = true ∧
    weights [5, 35, 51, 96, 17] pat102b = [102, 1632, 102, 306, 102] ∧ degSum pat102b = 19 ∧
    blockPattern 35 [1, 2, 16, 21, 30] 50 pat35 = true ∧
    weights [1, 2, 16, 21, 30] pat35 = [105, 35, 35, 35, 1050] ∧ degSum pat35 = 51 := by
  decide +kernel

/-- Theorem `thm:classes` for the levels 33 and 39. -/
theorem classes_33_39 :
    (List.range 33).filter (fun y => y * y % 33 == 1) = [1, 10, 23, 32] ∧
    (List.range 39).filter (fun y => y * y % 39 == 1) = [1, 14, 25, 38] ∧
    O33.filter (fun y => y * y % 33 == 1) = [1] ∧
    O39.filter (fun y => y * y % 39 == 1) = [1] ∧
    noPair 33 O33 = true ∧ noPair 39 O39 = true := by decide +kernel

/-! ## Section 8: the small levels of Shape III -/

/-- Nondecreasing triples from a list. -/
def triples (L : List Nat) : List (List Nat) :=
  L.flatMap (fun a => L.flatMap (fun b => L.filterMap (fun c =>
    if Nat.ble a b && Nat.ble b c then some [a, b, c] else none)))

theorem shape_three_levels :
    [1, 17, 12].sum = 30 ∧
    (triples [5, 10, 15]).filter (fun T => T.sum == 30) = [[5, 10, 15], [10, 10, 10]] ∧
    noPair 20 ([1, 17, 12] ++ [5, 10, 15]) = false ∧
    noPair 20 ([1, 17, 12] ++ [10, 10, 10]) = false ∧
    [1, 9, 25].sum = 35 ∧
    (triples [7, 14, 21]).filter (fun T => T.sum == 49) = [[7, 21, 21], [14, 14, 21]] ∧
    noPair 28 ([1, 9, 25] ++ [7, 21, 21]) = false ∧
    noPair 28 ([1, 9, 25] ++ [14, 14, 21]) = false ∧
    [1, 9, 17, 16, 20].sum + 21 = 84 ∧
    balanced 28 [1, 9, 16, 17, 20, 21] = true ∧
    msEq 28 (move 28 [1, 9, 16, 17, 20, 21] (tee 28 1) [1])
      [2, 9, 13, 14, 16, 17, 20, 21] = true ∧
    msEq 28 (move 28 [2, 9, 13, 14, 16, 17, 20, 21] (tee 28 6) [20, 16, 14])
      ([2, 9, 17] ++ [13, 21, 22]) = true ∧
    [2, 9, 17].sum % 28 = 0 ∧ [13, 21, 22].sum % 28 = 0 ∧
    [1, 13, 37, 41, 5, 24].sum = 121 ∧
    [7, 119, 84, 5, 45, 125].sum = 385 ∧ [7, 119, 84, 55, 75, 115].sum = 455 := by
  decide +kernel

/-! ## Section 10: the small local configurations of Table 3 and their completions -/

/-- Each row of the table of small local configurations, together with its
added elements, is a balanced multiset of four elements. -/
theorem small_completions :
    balanced 30 [1, 19, 25, 15] = true ∧ balanced 30 [1, 24, 20, 15] = true ∧
    balanced 60 [1, 49, 40, 30] = true ∧ balanced 15 [1, 6, 13, 10] = true ∧
    balanced 20 [1, 12, 17, 10] = true ∧ balanced 30 [1, 7, 27, 25] = true ∧
    balanced 60 [2, 21, 57, 40] = true ∧ balanced 28 [1, 9, 25, 21] = true ∧
    balanced 42 [1, 24, 38, 21] = true ∧ balanced 42 [1, 25, 37, 21] = true ∧
    balanced 42 [1, 30, 32, 21] = true ∧ balanced 66 [1, 25, 62, 44] = true ∧
    balanced 78 [1, 55, 61, 39] = true := by decide

/-- In the rows with two elements the added elements have smaller orders than
the largest order of the row. -/
theorem small_completions_lower :
    (ord 30 25 < 30 ∧ ord 30 15 < 30 ∧ ord 30 1 = 30) ∧
    (ord 30 20 < 30 ∧ ord 30 15 < 30 ∧ ord 30 1 = 30) ∧
    (ord 60 40 < 60 ∧ ord 60 30 < 60 ∧ ord 60 1 = 60) := by decide

/-! ## Section 9: the level 110 -/

def A110 : List Nat := [19, 29, 39, 55, 79, 109]

def nu110 (y : Nat) : Bool := y % 10 == 4 || y % 10 == 5 || y % 10 == 6

/-- Remark `rem:110` and its footnote. -/
theorem level_110 :
    balanced 110 A110 = true ∧ noPair 110 A110 = true ∧
    vanishesOnS 110 nu110 = true ∧ nuOf nu110 A110 = 1 ∧
    oddPrimes 110 = [5, 11] ∧
    nuOf (fun y => ord 110 y == 5) A110 = 0 ∧ nuOf (fun y => ord 110 y == 11) A110 = 0 ∧
    tee 110 1 = [1, 56, 108, 55] ∧
    (tee 110 1).filter (fun y => y * y % 110 == 1) = [1] := by decide +kernel

/-! ## Section 1: the first open degrees -/

def stripF : Nat → Nat → Nat → Nat
  | 0, _, M => M
  | fuel + 1, p, M => if Nat.ble 2 p && M % p == 0 && Nat.blt 0 M then stripF fuel p (M / p) else M

/-- `M` with all factors from `ps` removed. -/
def strip (M : Nat) (ps : List Nat) : Nat := ps.foldl (fun acc p => stripF acc p acc) M

/-- The least prime factor of `M`. -/
def spf (M : Nat) : Nat := nth ((List.range (M + 1)).filter (fun d => Nat.ble 2 d && M % d == 0)) 0

def primePower (M : Nat) : Bool := Nat.ble 2 M && strip M [spf M] == 1

/-- The degrees covered by the results quoted in the introduction: degree at
most 100 (da Silva), odd degree (Jumagulov up to 199, then every odd degree),
even degree up to 250 other than 110, 114, 220, 228 (Jumagulov's census),
prime powers and twice odd prime powers (Aoki), 2^a 3^b 5^c 7^d with 420 not
dividing M (Aoki, Peterson), 2^a 3^b 11^c and 2^a 3^b 13^c, and
2^a 3^b 17^c, 2^a 3^b 19^c with a at most 1. -/
def covered (M : Nat) : Bool :=
  Nat.ble M 100 || M % 2 == 1 ||
  (Nat.ble M 250 && !([110, 114, 220, 228].contains M)) ||
  primePower M || (M % 4 == 2 && primePower (M / 2)) ||
  (strip M [2, 3, 5, 7] == 1 && M % 420 != 0) ||
  strip M [2, 3, 11] == 1 || strip M [2, 3, 13] == 1 ||
  ((strip M [2, 3, 17] == 1 || strip M [2, 3, 19] == 1) && M % 4 != 0)

theorem first_open_degrees :
    (List.range 267).filter (fun M => M % 110 != 0 && !covered M) = [228, 258, 260, 266] := by
  decide +kernel

end FermatFourfolds

#print axioms FermatFourfolds.standard_examples
#print axioms FermatFourfolds.move_example
#print axioms FermatFourfolds.standard_balanced
#print axioms FermatFourfolds.standard_balanced_large
#print axioms FermatFourfolds.orbits_by_residues
#print axioms FermatFourfolds.orbits_cosets
#print axioms FermatFourfolds.orbits_balanced
#print axioms FermatFourfolds.orbits_identities
#print axioms FermatFourfolds.odd_case_facts
#print axioms FermatFourfolds.aoki_sets
#print axioms FermatFourfolds.parity_invariants
#print axioms FermatFourfolds.charpair_114
#print axioms FermatFourfolds.charpair_44
#print axioms FermatFourfolds.charpair_52
#print axioms FermatFourfolds.charpair_102
#print axioms FermatFourfolds.charpair_35
#print axioms FermatFourfolds.block_patterns
#print axioms FermatFourfolds.classes_33_39
#print axioms FermatFourfolds.shape_three_levels
#print axioms FermatFourfolds.small_completions
#print axioms FermatFourfolds.small_completions_lower
#print axioms FermatFourfolds.level_110
#print axioms FermatFourfolds.first_open_degrees
