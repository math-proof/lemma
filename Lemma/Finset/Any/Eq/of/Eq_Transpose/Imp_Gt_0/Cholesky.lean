import Lemma.Matrix.Any_And_Eq_Mul_Adjoint.of.PosDef
import Instance.LinearAlgebra.Matrix.GetElem
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
  obtain ⟨L, htri, hL⟩ := Any_And_Eq_Mul_Adjoint.of.PosDef hA
  have hlow : ∀ i j, i < j → L i j = 0 := fun i j hij => by
    simpa [getElem_getElem] using (htri j).1 i hij
  have hpos : ∀ i, 0 < L i i := fun i => by
    simpa [getElem_getElem] using (htri i).2
  refine ⟨L, hlow, fun i => ?_, by rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hL⟩
  have := (RCLike.pos_iff.mp (hpos i)).1
  simpa using this


-- created on 2023-07-02
-- updated on 2026-10-28
