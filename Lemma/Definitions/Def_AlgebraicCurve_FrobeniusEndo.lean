import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
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

def frobNorm (h : IsFrobeniusEndo ℓ φ) (f : F) : F :=
  (h.pow_mem_range f).choose

theorem map_frobNorm (h : IsFrobeniusEndo ℓ φ) (f : F) : φ (h.frobNorm f) = f ^ ℓ :=
  (h.pow_mem_range f).choose_spec

theorem frobNorm_ne_zero (h : IsFrobeniusEndo ℓ φ) {f : F} (hf : f ≠ 0) :
    h.frobNorm f ≠ 0 := by
  intro h0
  have := h.map_frobNorm f
  rw [h0, map_zero] at this
  exact pow_ne_zero ℓ hf this.symm

theorem isIntegral (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) : φ.toRingHom.IsIntegral := by
  intro x
  refine ⟨Polynomial.X ^ ℓ - Polynomial.C (h.frobNorm x), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ hℓ
  · simp [Polynomial.eval₂_sub, h.map_frobNorm x]

end IsFrobeniusEndo

end Package

end AlgebraicCurve
