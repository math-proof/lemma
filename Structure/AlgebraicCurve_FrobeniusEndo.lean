import Lemma.AlgebraicCurve.Correspondence
import Mathlib.Algebra.CharP.Reduced

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Package

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (ℓ : ℕ)

structure IsFrobeniusEndo (φ : F →ₐ[K] F) : Prop where

  pow_mem_range : ∀ x : F, ∃ y : F, φ y = x ^ ℓ

  mem_range_pow : ∀ y : F, ∃ x : F, φ y = x ^ ℓ

variable {ℓ : ℕ} {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo


end IsFrobeniusEndo

end Package

end AlgebraicCurve
