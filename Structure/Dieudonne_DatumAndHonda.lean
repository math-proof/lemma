import Mathlib

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞]

@[ext]
structure DieudonneDatum (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] where

  F : D →ₗ[𝓞] D

  V : D →ₗ[𝓞] D

  fv : F ∘ₗ V = ℓ • LinearMap.id

  vf : V ∘ₗ F = ℓ • LinearMap.id

namespace DieudonneDatum

variable {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D] (M : DieudonneDatum ℓ D)


variable (ℓ) in


variable (ℓ) in


end DieudonneDatum

structure HondaSystem (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] extends
    DieudonneDatum ℓ D where

  L : Submodule 𝓞 D

  sh1_le : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y

  sh1_ge : ∀ y ∈ L, ℓ • y ∈ LinearMap.range F

  sh2' : (LinearMap.range F) ⊔ L = ⊤

  sh3 : ∀ x ∈ L, V x = 0 → x = 0

end Deformation
