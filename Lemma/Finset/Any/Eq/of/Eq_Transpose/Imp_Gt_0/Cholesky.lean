import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : Aᵀ = A)
  (h₁ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℝ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᵀ := by
-- proof
  have hA : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    ·
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h₀]
    ·
      rw [star_trivial]
      exact h₁ x hx
  obtain ⟨L, hlow, hpos, hL⟩ := Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA
  refine ⟨L, hlow, fun i => ?_, by rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hL⟩
  have := (RCLike.pos_iff.mp (hpos i)).1
  simpa using this


-- created on 2023-07-02
