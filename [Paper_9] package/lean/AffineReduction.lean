import Mathlib.Algebra.Module.Submodule.Lattice

/-!
Elementary subspace lemmas for a written repair of the F2 reduction.
This file has no model of varieties, Hodge classes, or algebraic cycles.
It does not prove F2, F3', or the Hodge conjecture.
-/

namespace HodgeReductionAudit

variable {K M : Type*} [Ring K] [AddCommGroup M] [Module K M]

theorem outside_add_inside (R : Submodule K M) {e r : M}
    (he : e ∉ R) (hr : r ∈ R) : e + r ∉ R := by
  intro h
  have he' := R.sub_mem h hr
  exact he (by simpa using he')

theorem affine_difference (R C : Submodule K M)
    (outside_algebraic : ∀ x : M, x ∉ R → x ∈ C)
    {e r : M} (he : e ∉ R) (hr : r ∈ R) : r ∈ C := by
  have heC := outside_algebraic e he
  have herC := outside_algebraic (e + r) (outside_add_inside R he hr)
  have hrC := C.sub_mem herC heC
  simpa [add_comm] using hrC

theorem proper_complement_spans (R C : Submodule K M)
    (outside_algebraic : ∀ x : M, x ∉ R → x ∈ C)
    (proper : ∃ e : M, e ∉ R) : C = ⊤ := by
  apply top_unique
  intro r _
  obtain ⟨e, he⟩ := proper
  by_cases hr : r ∈ R
  · exact affine_difference R C outside_algebraic he hr
  · exact outside_algebraic r hr

#print axioms outside_add_inside
#print axioms affine_difference
#print axioms proper_complement_spans

end HodgeReductionAudit
