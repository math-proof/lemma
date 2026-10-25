import Mathlib

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

def deuringCurve (α β : R) : WeierstrassCurve R := ⟨α, 0, β, 0, 0⟩


variable (W : WeierstrassCurve R)

def deuringA₃ (x y : R) : R := 2 * y + W.a₁ * x + W.a₃

def tangentSlopeNum (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

noncomputable def tangentSlope (x y : R) : R := W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x y)

noncomputable def deuringA₁ (x y : R) : R := W.a₁ + 2 * W.tangentSlope x y

def flexForm (x y : R) : R :=
  W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
    - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2

noncomputable def deuringVariableChange (x₁ y₁ : R) (u : Rˣ) : VariableChange R :=
  ⟨u, x₁, W.tangentSlope x₁ y₁, y₁⟩

noncomputable def levelThreeModulus (x₁ y₁ x₂ : R) : R :=
  W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁)

noncomputable def levelThreeAbscissa (x₁ y₁ x₂ : R) : R :=
  (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2

noncomputable def levelThreeOrdinate (x₁ y₁ x₂ y₂ : R) : R :=
  (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 3

end WeierstrassCurve
