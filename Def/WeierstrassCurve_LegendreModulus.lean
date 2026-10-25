import Mathlib
import Def.WeierstrassCurve_HasseInvariant

namespace WeierstrassCurve

variable {F : Type*} [Field F]

def thirdTwoTorsionX (W : WeierstrassCurve F) (x₁ x₂ : F) : F := -W.b₂ / 4 - x₁ - x₂

def legendreLambda (W : WeierstrassCurve F) (x₁ x₂ : F) : F :=
  (W.thirdTwoTorsionX x₁ x₂ - x₁) / (x₂ - x₁)

def legendreVariableChange (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) : VariableChange F :=
  ⟨Units.mk0 w hw, x₁, -W.a₁ / 2, -(W.a₃ + x₁ * W.a₁) / 2⟩

end WeierstrassCurve
