import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {L : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : Aᵀ = A)
  (h₁ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * L j k) / L j j else if j = i then Real.sqrt (A i i - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) else 0) :
-- imply
  A = L * Lᵀ := by
-- proof
  have hA : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    ·
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h₀]
    ·
      rw [star_trivial]
      exact h₁ x hx
  have hrec : IsCholeskyRec A L := by
    intro i j
    rw [h₂ i j]
    simp only [star_trivial, RCLike.re_to_real, RCLike.ofReal_real_eq_id, id]
  have h := (All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA hrec).2.2
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h


-- created on 2023-05-01
