import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A B C D : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  A * (B - C) * D = -(A * (C - B) * D) := by
-- proof
  rw [show B - C = -(C - B) by abel, Matrix.mul_neg, Matrix.neg_mul]


-- created on 2023-04-30
