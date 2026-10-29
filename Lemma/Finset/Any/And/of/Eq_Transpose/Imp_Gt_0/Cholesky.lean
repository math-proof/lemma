import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
import Instance.LinearAlgebra.Matrix.GetElem
import Lemma.Matrix.Any_And_Eq_Mul_Adjoint.of.PosDef
open Matrix


@[path]
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
  obtain ⟨L, htri, hL⟩ := Any_And_Eq_Mul_Adjoint.of.PosDef hA
  have hlow : ∀ i j, i < j → L i j = 0 := fun i j hij => by
    simpa [getElem_getElem] using (htri j).1 i hij
  have hpos : ∀ i, 0 < L i i := fun i => by
    simpa [getElem_getElem] using (htri i).2
  have h := IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
  rw [← hL] at h
  refine ⟨L, by rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hL, fun i j => ?_⟩
  have hij := h i j
  simp only [star_trivial, RCLike.re_to_real, RCLike.ofReal_real_eq_id, id] at hij
  exact hij


-- created on 2023-07-02
-- updated on 2026-10-28
