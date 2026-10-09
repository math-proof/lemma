import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.Lt_Sum_SquareNorm.et.All_Eq_Sum_Mul_Star.of.All_And.All_Eq_Div.PosDef
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {L : Matrix (Fin n) (Fin n) ℝ}
  {t : Fin n}
-- given
  (h₀ : Aᵀ = A)
  (h₁ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, j < i → L i j = (A i j - ∑ k ∈ Finset.Iio j, L i k * L j k) / L j j)
  (h₃ : ∀ i, i < t → A i i = ∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 ∧ 0 < L i i ∧ ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * L j k) :
-- imply
  ∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 < A t t ∧ ∀ j, j < t → A t j = ∑ k ∈ Finset.Iic j, L t k * L j k := by
-- proof
  have hA : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    ·
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h₀]
    ·
      rw [star_trivial]
      exact h₁ x hx
  obtain ⟨p, q⟩ := Lt_Sum_SquareNorm.et.All_Eq_Sum_Mul_Star.of.All_And.All_Eq_Div.PosDef hA (L := L) (fun i j h => by rw [h₂ i j h]; simp only [star_trivial]) t
    (fun i hi => by
      obtain ⟨a, b, c⟩ := h₃ i hi
      exact ⟨by rw [a]; simp, RCLike.pos_iff.mpr ⟨by simpa using b, by simp⟩, fun j hj => by rw [c j hj]; simp only [star_trivial]⟩)
  refine ⟨by simpa using (RCLike.lt_iff_re_im.mp p).1, fun j hj => ?_⟩
  rw [q j hj]
  simp only [star_trivial]


-- created on 2023-06-29
