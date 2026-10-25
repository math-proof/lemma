import Lemma.TaylorWiles.Primes
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Def.LanglandsTunnell_TowerCounting

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField Ideal FrobeniusDensity


variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]


theorem labelledCount_of_mem_S₀ (σ : L ≃ₐ[ℚ] L) (S₀ : Finset ℕ) (m : Fin 8) {ℓ : ℕ}
    (h : ℓ ∈ S₀) : labelledCount σ S₀ m ℓ = 0 := by
  simp [labelledCount, h]


theorem classIndicator_le_one (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : classIndicator σ ℓ ≤ 1 := by
  unfold classIndicator; split <;> simp

end LanglandsTunnell
