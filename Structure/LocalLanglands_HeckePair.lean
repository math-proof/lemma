import Mathlib
import Instance.AbstractHeckeOperator
import Instance.LocalLanglands_HeckePair

set_option autoImplicit false

open scoped Pointwise
open Function MulAction

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀} in

structure IsHeckeFun (f : G → R₀) : Prop where

  left_inv : ∀ u ∈ U, ∀ x, f (u * x) = f x

  right_inv : ∀ u ∈ U, ∀ x, f (x * u) = f x

  finite_cosets : ((QuotientGroup.mk '' (Function.support f)) : Set (G ⧸ U)).Finite

variable {U R₀} in


variable {U R₀} in


variable {U R₀} in


variable {U R₀}


variable (U R₀) in


variable (U) in


variable (R₀) in


end
end HeckePair
