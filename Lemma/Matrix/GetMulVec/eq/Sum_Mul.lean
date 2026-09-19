import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  [Fintype n]
-- given
  (A : Matrix m n ℝ)
  (x : n → ℝ)
  (j : m) :
-- imply
  (A *ᵥ x) j = ∑ i, A j i * x i := by
-- proof
  simp [Matrix.mulVec, dotProduct]


-- created on 2026-09-19
