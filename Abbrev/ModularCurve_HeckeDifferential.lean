import Mathlib
import Lemma.ModularCurve.HeckeOperator
import Def.AlgebraicCurve_DifferentialPushPull
import Def.AlgebraicCurve_RegularDifferentials
import Instance.ModularCurve_HeckeDifferential

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve

namespace ModularCurve

section Euler

variable (R : Type*) [CommRing R]

end Euler

section Shortcuts

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

end Shortcuts

section QExpansion

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

end QExpansion

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

end Hecke

section Bar

variable (N : ℕ)

variable [NeZero N]

abbrev regularDifferentialsBar : Submodule (AlgebraicClosure ℚ)
    Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  regularDifferentials (AlgebraicClosure ℚ) (modularFunctionFieldBar N)

end Bar

end ModularCurve

end
