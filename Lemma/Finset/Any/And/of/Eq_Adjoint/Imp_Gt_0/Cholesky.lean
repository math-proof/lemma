import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℂ, A = L * Lᴴ ∧ ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0 := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨L, hlow, hpos, hL⟩ := hA.exists_cholesky
  have h := IsCholeskyRec.of_factor hlow hpos
  rw [← hL] at h
  exact ⟨L, hL, h⟩


-- created on 2026-09-27
