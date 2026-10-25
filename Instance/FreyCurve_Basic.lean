-- Carved from Lemma/Definitions/Def_FreyCurve_Basic.lean: instance decls only.
import Mathlib
set_option autoImplicit false

namespace FreyCurve
open FreyPackage


instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num


end FreyCurve
