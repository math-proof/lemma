import Mathlib
import sympy.Basic


/--
[IntermediateField_exists_mulEquiv_fixedField_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_mulEquiv_fixedField_apply_eq.lean)
-/
@[path]
private lemma main
  [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
  {H : Subgroup (F ≃ₐ[E] F)} :
-- imply
  ∃ Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y := by
-- proof
  refine ⟨(MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)), fun s y => ?_⟩
  rfl


-- created on 2026-10-03
