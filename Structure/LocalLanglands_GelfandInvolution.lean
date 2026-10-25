import Mathlib
import Instance.LocalLanglands_HeckePair

set_option autoImplicit false

open scoped Pointwise

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G}
variable {R₀ : Type*} [CommRing R₀]


variable (U) in

structure IsGelfandInvolution (τ : G → G) : Prop where

  map_mul : ∀ x y, τ (x * y) = τ y * τ x

  involutive : ∀ x, τ (τ x) = x

  map_mem : ∀ u ∈ U, τ u ∈ U

  mem_doubleCoset : ∀ g, τ g ∈ doubleCoset U g

namespace IsGelfandInvolution

variable {τ : G → G} (hτ : IsGelfandInvolution U τ)

include hτ


end IsGelfandInvolution


end

end HeckePair
