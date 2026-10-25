import Mathlib

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]

def pointAddEquivOfEq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

end WeierstrassCurve
