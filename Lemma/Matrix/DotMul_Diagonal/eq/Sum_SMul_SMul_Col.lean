import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  [DecidableEq n] [Fintype n]
-- given
  (d : n → ℝ)
  (x : n → ℝ)
  (A : Matrix m n ℝ) :
-- imply
  (A * Matrix.diagonal d) *ᵥ x = ∑ i, d i • x i • A.col i := by
-- proof
  ext j
  simp [Matrix.mul_diagonal, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring_nf


-- created on 2026-09-19
