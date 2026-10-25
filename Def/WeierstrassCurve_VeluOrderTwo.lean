import Mathlib
import Def.WeierstrassCurve_Velu

set_option autoImplicit false

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotient2 (x₀ y₀ : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluGx x₀ y₀
  a₆ := W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)

variable (x₀ y₀ : R)


def velu2QuadDisc (x₀ : R) : R :=
  W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄

end CommRing

end WeierstrassCurve
