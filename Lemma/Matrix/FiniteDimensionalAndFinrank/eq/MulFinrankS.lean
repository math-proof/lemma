import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraNotes.code.FieldExtensions
open FieldExtensions


namespace FieldExtensions

/--
[tower_law](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean)
-/
@[path]
lemma tower_law
  {F E K : Type*}
  [Field F]
  [Field E]
  [Field K]
  [Algebra F E]
  [Algebra E K]
  [Algebra F K]
  [IsScalarTower F E K]
  [FiniteDimensional F E]
  [FiniteDimensional E K] :
-- imply
  FiniteDimensional F K ∧ Module.finrank F K = Module.finrank F E * Module.finrank E K :=
-- proof
  ⟨FiniteDimensional.trans F E K, (Module.finrank_mul_finrank F E K).symm⟩

end FieldExtensions

namespace FieldExtensions

/--
[finiteDimensional_tower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean)
-/
@[path]
lemma finiteDimensional_tower_iff
  {K F E : Type*}
  [Field K]
  [Field F]
  [Field E]
  [Algebra K F]
  [Algebra F E]
  [Algebra K E]
  [IsScalarTower K F E] :
-- imply
  (Module.finrank K F * Module.finrank F E = Module.finrank K E) ∧ (FiniteDimensional K E ↔ FiniteDimensional K F ∧ FiniteDimensional F E) := by
-- proof
  refine ⟨Module.finrank_mul_finrank K F E, ?_⟩
  constructor
  · intro h
    exact ⟨FiniteDimensional.left K F E, FiniteDimensional.right K F E⟩
  · intro ⟨h1, h2⟩
    exact FiniteDimensional.trans K F E

end FieldExtensions

namespace FieldExtensions

/--
[algebraic_operations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean)
-/
@[path]
lemma algebraic_operations
  [Field K]
  [Field L]
  [Algebra K L]
  {α β : L}
-- given
  (hα : IsAlgebraic K α)
  (hβ : IsAlgebraic K β) :
-- imply
  IsAlgebraic K (α + β) ∧ IsAlgebraic K (α * β) ∧ IsAlgebraic K (α / β) :=
-- proof
  ⟨hα.add hβ, hα.mul hβ, div_eq_mul_inv α β ▸ hα.mul (IsAlgebraic.inv_iff.mpr hβ)⟩

end FieldExtensions

namespace FieldExtensions

/--
[isAlgebraic_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean)
-/
@[path]
lemma isAlgebraic_def
  [Field K]
  [Field L]
  [Algebra K L]
  {α : L} :
-- imply
  IsAlgebraic K α ↔ ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.aeval α p = 0 :=
-- proof
  Iff.rfl

end FieldExtensions

namespace FieldExtensions

/--
[isAlgebraic_iff_adjoin_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean)
-/
@[path]
lemma isAlgebraic_iff_adjoin_finiteDimensional
  [Field K]
  [Field L]
  [Algebra K L]
  {α : L} :
-- imply
  IsAlgebraic K α ↔ FiniteDimensional K ↥(IntermediateField.adjoin K {α}) := by
-- proof
  rw [isAlgebraic_iff_isIntegral]
  constructor
  · exact IntermediateField.adjoin.finiteDimensional
  · intro h
    have hgen := IsIntegral.of_finite K (IntermediateField.AdjoinSimple.gen K α)
    have hcast : (algebraMap (↥(IntermediateField.adjoin K {α})) L)
      (IntermediateField.AdjoinSimple.gen K α) = α :=
      IntermediateField.AdjoinSimple.algebraMap_gen K α
    rwa [← hcast]

end FieldExtensions


-- created on 2026-10-23
