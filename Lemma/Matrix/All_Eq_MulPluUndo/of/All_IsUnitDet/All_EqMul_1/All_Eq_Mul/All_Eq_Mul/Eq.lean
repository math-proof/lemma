import sympy.matrices.plu
import sympy.Basic
open Matrix


/-- Telescoping form of a PLU sweep: `X = (S 0)ᵀ (L 0)⁻¹ ⋯ (S (m-1))ᵀ (L (m-1))⁻¹ A m`. -/
@[path]
private lemma main
  {n : ℕ}
  {X : Matrix (Fin n) (Fin n) ℂ}
  {A B S L : ℕ → Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : X = A 0)
  (h₁ : ∀ k, B k = S k * A k)
  (h₂ : ∀ k, A (k + 1) = L k * B k)
  (h₃ : ∀ k, (S k)ᵀ * S k = 1)
  (h₄ : ∀ k, IsUnit (L k).det) :
-- imply
  ∀ m, X = pluUndo S L m * A m := by
-- proof
  intro m
  induction m with
  | zero =>
    rw [h₀, pluUndo, Matrix.one_mul]
  | succ m ih =>
    rw [ih, pluUndo, h₂ m, h₁ m]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L m)⁻¹ (L m), Matrix.nonsing_inv_mul _ (h₄ m), Matrix.one_mul,
      ← Matrix.mul_assoc (S m)ᵀ, h₃ m, Matrix.one_mul]


-- created on 2026-10-07
