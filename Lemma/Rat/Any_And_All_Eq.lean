import Mathlib
import sympy.Basic

open IntermediateField

/--
[IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.lean)
-/
@[main]
private lemma main
  {K : Type u} [Field K]
  {Ω : Type v} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {x : Ω} :
-- imply
  ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by
-- proof
  exact
    ⟨IntermediateField.adjoin K {x},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x),
      fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ x
        (IntermediateField.subset_adjoin K _ (Set.mem_singleton x))⟩


-- created on 2026-10-05
