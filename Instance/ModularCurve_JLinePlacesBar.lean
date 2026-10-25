-- Carved from Lemma/Definitions/Def_ModularCurve_JLinePlacesBar.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_ArithmeticGalois
import Instance.AlgebraicCurve_RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Def.ModularCurve_JLinePlacesBar

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (N : ℕ) [NeZero N]

instance instAlgebraJLineBar : Algebra (AlgebraicClosure ℚ) ↥(jLineBar N) := IntermediateField.algebra' (jLineBar N)

instance instModuleJLineBar : Module (AlgebraicClosure ℚ) ↥(jLineBar N) := Algebra.toModule


end ModularCurve

end
