import Def.WeierstrassCurve_Velu

set_option autoImplicit false

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotientOfSums (t w : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * t
  a₆ := W.a₆ - W.b₂ * t - 7 * w

end WeierstrassCurve
