import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[path]
private lemma scaled_dot_product_attention
  {n d : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin n) (Fin d) ℝ} :
-- imply
  (Matrix.of fun i j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) * V =
    Matrix.of fun i l => (∑ j, V j l * Real.exp (A i j)) / ∑ k, Real.exp (A i k) := by
-- proof
  ext i l
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring


-- created on 2023-06-18
