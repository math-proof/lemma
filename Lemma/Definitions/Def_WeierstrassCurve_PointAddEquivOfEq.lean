import Mathlib

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]

def pointAddEquivOfEq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

@[simp] theorem pointAddEquivOfEq_refl (W : WeierstrassCurve L) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ := rfl

theorem pointAddEquivOfEq_symm {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    (pointAddEquivOfEq e).symm = pointAddEquivOfEq e.symm := by subst e; rfl

theorem pointAddEquivOfEq_some {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂)
    {x y : L} (h : W₁.toAffine.Nonsingular x y) :
    pointAddEquivOfEq e (.some x y h) = .some x y (e ▸ h) := by subst e; rfl

end WeierstrassCurve
