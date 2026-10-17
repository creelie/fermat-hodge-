/-
FermatFourfolds.lean

Kernel-checked finite arithmetic behind the paper
"The Hodge conjecture for Fermat fourfolds of degree not divisible by 110".

Nothing here formalises algebraic geometry. A multiset of residues modulo M
is a list of natural numbers; it is balanced when its sum is 0 modulo M, no
entry is 0 modulo M, and for every unit t the representatives of t*a add up
to (number of entries) * M / 2.

No Mathlib. Every theorem is checked by `decide`; the block at the end prints
the axioms of each one.
-/

set_option maxRecDepth 100000

namespace FermatFourfolds

/-- `h t` for the multiset `A` at level `M`: the sum of the representatives
of `t * a` in `0, ..., M - 1`. -/
def hsum (M t : Nat) (A : List Nat) : Nat := (A.map (fun a => t * a % M)).sum

/-- The balancing condition of the paper, as a Boolean. -/
def balanced (M : Nat) (A : List Nat) : Bool :=
  (A.sum % M == 0) && A.all (fun a => a % M != 0) &&
  (List.range M).all (fun t => Nat.gcd t M != 1 || hsum M t A * 2 == A.length * M)

/-! ## Section 9: the small local configurations of Table 2 and their completions -/

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

/-- The additive order of `y` modulo `M`. -/
def ord (M y : Nat) : Nat := M / Nat.gcd y M

/-- In the rows with two elements the added elements have smaller orders than
the largest order of the row. -/
theorem small_completions_lower :
    (ord 30 25 < 30 ∧ ord 30 15 < 30 ∧ ord 30 1 = 30) ∧
    (ord 30 20 < 30 ∧ ord 30 15 < 30 ∧ ord 30 1 = 30) ∧
    (ord 60 40 < 60 ∧ ord 60 30 < 60 ∧ ord 60 1 = 60) := by decide

end FermatFourfolds

#print axioms FermatFourfolds.small_completions
#print axioms FermatFourfolds.small_completions_lower
