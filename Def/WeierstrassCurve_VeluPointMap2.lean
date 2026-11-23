module

public import Mathlib
public import Theorem.WeierstrassCurve.VeluOrderTwo

@[expose] public section

set_option autoImplicit false

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)

def velu2XNum (x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀)

def velu2YNum (x y : R) : R :=
  y * (x - x₀) ^ 3 - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def velu2X (x₀ y₀ x : F) : F :=
  x + W.veluGx x₀ y₀ / (x - x₀)

noncomputable def velu2Y (x₀ y₀ x y : F) : F :=
  y - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2


variable {W}
variable (hchar : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

open scoped Classical in
set_option linter.unusedVariables false in

noncomputable def veluPointMap2 :
    W.toAffine.Point → (W.veluQuotient2 x₀ y₀).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x = x₀ then .zero
    else .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ)

end Field

end WeierstrassCurve

end
