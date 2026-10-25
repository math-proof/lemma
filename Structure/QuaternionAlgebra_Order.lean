import Mathlib

set_option autoImplicit false

namespace QuaternionAlgebra

open scoped Quaternion

variable {a b : ℚ}

structure IsOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where

  one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ

  mul_mem : ∀ ⦃x y : ℍ[ℚ, a, b]⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ

  spanTop : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤

  fg : Λ.FG


end QuaternionAlgebra
