import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : Aᵀ = A)
  (h₁ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℝ, A = L * Lᵀ ∧ ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * L j k) / L j j else if j = i then Real.sqrt (A i i - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) else 0 := by
-- proof
  have hA : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    ·
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h₀]
    ·
      rw [star_trivial]
      exact h₁ x hx
  obtain ⟨L, hlow, hpos, hL⟩ := Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA
  have h := IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
  rw [← hL] at h
  refine ⟨L, by rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hL, fun i j => ?_⟩
  have hij := h i j
  simp only [star_trivial, RCLike.re_to_real, RCLike.ofReal_real_eq_id, id] at hij
  exact hij


-- created on 2023-07-02
