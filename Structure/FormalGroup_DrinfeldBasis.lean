import Mathlib
import Def.FormalGroup_NSeries
import Def.FormalGroup_DrinfeldBasis

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {T : Type*} [CommRing T] [UniformSpace T]


structure DrinfeldLevel (F : FormalGroup T) (q : ℕ) (e : T → T → T) (ζ : T) where

  x₀ : T

  x₁ : T

  isDrinfeldBasis : F.IsDrinfeldBasis q x₀ x₁

  pairing_eq : e x₀ x₁ = ζ

section Adic

variable {T : Type*} [CommRing T]


end Adic

end FormalGroup

end
