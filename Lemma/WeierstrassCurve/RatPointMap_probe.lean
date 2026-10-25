import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.WeierstrassCurve_RatPointMap_probe

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F k : Type} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

private theorem some_congr {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

end WeierstrassCurve
