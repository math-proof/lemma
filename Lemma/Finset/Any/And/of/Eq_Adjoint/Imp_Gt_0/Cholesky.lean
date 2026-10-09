import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
open Matrix
open scoped ComplexOrder


@[path]
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
  obtain ⟨L, hlow, hpos, hL⟩ := Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA
  have h := IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
  rw [← hL] at h
  exact ⟨L, hL, h⟩


-- created on 2023-07-01
