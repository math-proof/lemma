import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Class.WeierstrassCurve_GenusOnePic0

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable {W : Affine F} [GenusOnePlaceGate W]

abbrev pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  GenusOnePlaceGate.pointEquivPlace (W := W)

section AbelTheorem

variable [AbelTheorem W]

end AbelTheorem

end WeierstrassCurve.Affine

end
