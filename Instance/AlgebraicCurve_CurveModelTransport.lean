-- Carved from Lemma/Definitions/Def_AlgebraicCurve_CurveModelTransport.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicCurve.CurveModel
import Lemma.AlgebraicCurve.CurveModelTransport

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicCurve

section FunctionFieldIso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

instance isIso_functionFieldHomOfIso (e : X ≅ Y) : IsIso (functionFieldHomOfIso e) := by
  haveI := isIso_stalkSpecializes_of_eq (inv_base_genericPoint e)
  exact IsIso.comp_isIso

end FunctionFieldIso


end AlgebraicCurve

end
