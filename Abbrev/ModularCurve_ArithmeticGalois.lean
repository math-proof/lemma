import Structure.ModularCurve_X0
import Def.ModularCurve_LaurentCoeff
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Rat

namespace ModularCurve

section ArithmeticGalois

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

end ArithmeticGalois

section PicAction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

end PicAction

section ModularInstance

variable (N : ℕ)

abbrev modularFunctionFieldBar : IntermediateField (AlgebraicClosure ℚ)
    (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

abbrev JZero : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)

end ModularInstance

end ModularCurve
