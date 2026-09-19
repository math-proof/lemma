import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  [Fintype m]
-- given
  (c : ℝ)
  (v : m → ℝ)
  (A : Matrix m n ℝ) :
-- imply
  (c • v) ᵥ* A = c • (v ᵥ* A) := by
-- proof
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]


-- created on 2026-09-19
