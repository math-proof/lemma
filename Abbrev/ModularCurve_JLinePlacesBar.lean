import Mathlib
import Instance.ModularCurve_ArithmeticGalois
import Instance.AlgebraicCurve_RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (N : ℕ) [NeZero N]

abbrev jLineBar : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ)
    {(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      ↥(modularFunctionFieldBar N))}

end ModularCurve

end
