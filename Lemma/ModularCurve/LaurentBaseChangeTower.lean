import Mathlib
import Lemma.ModularCurve.LaurentCoeff
import Instance.ModularCurve_LaurentBaseChangeTower

noncomputable section

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

section Tower

def baseChangeRingHom : F₀ →+* laurentBaseChange L F₀ where
  toFun y := ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩
  map_one' := Subtype.ext (map_one (coeffEmb L))
  map_mul' _ _ := Subtype.ext (map_mul (coeffEmb L) _ _)
  map_zero' := Subtype.ext (map_zero (coeffEmb L))
  map_add' _ _ := Subtype.ext (map_add (coeffEmb L) _ _)

@[simp]
theorem coe_baseChangeRingHom (y : F₀) :
    (baseChangeRingHom L F₀ y : LaurentSeries L) = coeffEmb L (y : LaurentSeries ℚ) :=
  rfl

@[reducible] def baseChangeAlgebra : Algebra F₀ (laurentBaseChange L F₀) :=
  (baseChangeRingHom L F₀).toAlgebra

attribute [local instance] baseChangeAlgebra

theorem algebraMap_laurentBaseChange_eq :
    algebraMap F₀ (laurentBaseChange L F₀) = baseChangeRingHom L F₀ :=
  rfl

@[reducible] def baseChangeAlgebraRat : Algebra ℚ (laurentBaseChange L F₀) :=
  ((algebraMap L (laurentBaseChange L F₀)).comp (algebraMap ℚ L)).toAlgebra

attribute [local instance] baseChangeAlgebraRat

end Tower

end ModularCurve

end
