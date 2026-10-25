import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.AlgebraicNumbers
open AlgebraicNumber
open NumberField


namespace AlgebraicNumber

/--
[isAlgebraicNumber_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicNumbers.lean)
-/
@[path]
lemma isAlgebraicNumber_iff
  {α : ℂ} :
-- imply
  IsAlgebraicNumber α ↔ IsAlgebraic ℚ α :=
-- proof
  Iff.rfl

end AlgebraicNumber

namespace AlgebraicNumber

/--
[isAlgebraicInteger_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicNumbers.lean)
-/
@[path]
lemma isAlgebraicInteger_iff
  {α : ℂ} :
-- imply
  IsAlgebraicInteger α ↔ IsIntegral ℤ α :=
-- proof
  Iff.rfl
open NumberField

end AlgebraicNumber

namespace AlgebraicNumber

/--
[ringOfIntegers_isMaximalOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicNumbers.lean)
-/
@[path]
lemma ringOfIntegers_isMaximalOrder
  {K : Type*}
  [Field K]
  [NumberField K]
  {O : Subalgebra ℤ K}
  [Module.Finite ℤ O] :
-- imply
  O ≤ integralClosure ℤ K := by
-- proof
  intro x hx
  exact (IsIntegral.of_finite ℤ (⟨x, hx⟩ : O)).algebraMap

end AlgebraicNumber


-- created on 2026-10-23
