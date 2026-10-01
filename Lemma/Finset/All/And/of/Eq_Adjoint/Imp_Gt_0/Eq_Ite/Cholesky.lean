import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
  {L : Matrix (Fin n) (Fin n) ℂ}
  {t : ℕ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0) :
-- imply
  ∀ i : Fin n, i.val < t → 0 < L i i ∧ A i i = ((∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 : ℝ) : ℂ) ∧ ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * star (L j k) := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨hlow, hpos, hL⟩ := hA.cholesky_of_rec h₂
  have hs : ∀ i j, A i j = ∑ k ∈ Finset.Iic j, L i k * star (L j k) := by
    intro i j
    rw [hL, Matrix.mul_conjTranspose_apply_of_lower hlow, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
  intro i _hi
  refine ⟨hpos i, ?_, fun j _ => hs i j⟩
  rw [hs i i]
  simp only [RCLike.star_def, RCLike.mul_conj]
  push_cast
  rfl


-- created on 2023-05-01
