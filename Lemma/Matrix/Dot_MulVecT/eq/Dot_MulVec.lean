import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  [Fintype m]
-- given
  (A : Matrix m m ℝ)
  (x y : m → ℝ) :
-- imply
  x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
-- proof
  rw [Matrix.dotProduct_mulVec]
  rw [dotProduct_comm]
  rw [Matrix.vecMul_transpose]


-- created on 2026-09-19
