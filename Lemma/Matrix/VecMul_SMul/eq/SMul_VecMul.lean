import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  {m n : Type*} [Fintype m]
-- given
  (v : m → ℝ)
  (c : ℝ)
  (A : Matrix m n ℝ) :
-- imply
  v ᵥ* (c • A) = c • (v ᵥ* A) := by
-- proof
  funext j
  simp [Matrix.vecMul, Pi.smul_apply, dotProduct, Finset.mul_sum, mul_left_comm]


-- created on 2026-09-19
