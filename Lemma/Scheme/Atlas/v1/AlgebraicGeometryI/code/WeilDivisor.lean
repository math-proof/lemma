import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor
open WeilDivisor


namespace WeilDivisor

/--
[isEffective_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean)
-/
@[path]
lemma isEffective_zero
  {Y : Type*} :
-- imply
  IsEffective (0 : WeilDivisor.Group Y) := by
-- proof
  intro y; simp

end WeilDivisor

namespace WeilDivisor

/--
[isEffective_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean)
-/
@[path]
lemma isEffective_add
  {D₁ D₂ : WeilDivisor.Group Y}
-- given
  (h₁ : IsEffective D₁)
  (h₂ : IsEffective D₂) :
-- imply
  IsEffective (D₁ + D₂) := by
-- proof
  intro y
  simp [Finsupp.add_apply]
  exact add_nonneg (h₁ y) (h₂ y)

end WeilDivisor


-- created on 2026-10-23
