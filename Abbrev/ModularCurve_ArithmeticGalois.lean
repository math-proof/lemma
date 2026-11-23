module

public import Structure.ModularCurve_X0
public import Theorem.HahnSeries.X0
public import Def.ModularCurve_LaurentCoeff
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

@[expose] public noncomputable section

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
