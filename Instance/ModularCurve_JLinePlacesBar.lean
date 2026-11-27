module
public import Mathlib
public import Instance.ModularCurve_ArithmeticGalois
public import Instance.AlgebraicCurve_RatFuncPlaces
public import Theorem.Valuation.RatFuncPlaceInfty
public import Theorem.Thm_ModularCurve_transcendental_coeffEmb_jq
public import Def.ModularCurve_JLinePlacesBar
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_JLinePlacesBar.lean: instance decls only.

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (N : ℕ) [NeZero N]

instance instAlgebraJLineBar : Algebra (AlgebraicClosure ℚ) ↥(jLineBar N) := IntermediateField.algebra' (jLineBar N)

instance instModuleJLineBar : Module (AlgebraicClosure ℚ) ↥(jLineBar N) := Algebra.toModule


end ModularCurve

end
