import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
  {L : Matrix (Fin n) (Fin n) ℂ}
  {t : Fin n}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, j < i → L i j = (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j)
  (h₃ : ∀ i, i < t → A i i = ((∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 : ℝ) : ℂ) ∧ 0 < L i i ∧ ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * star (L j k)) :
-- imply
  ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : ℂ) < A t t ∧ ∀ j, j < t → A t j = ∑ k ∈ Finset.Iic j, L t k * star (L j k) := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  exact hA.cholesky_step h₂ t h₃


-- created on 2023-06-22
