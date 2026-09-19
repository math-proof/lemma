import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  [Fintype m] [DecidableEq m]
-- given
  (d x y : m → ℝ) :
-- imply
  x ᵥ* Matrix.diagonal d ⬝ᵥ y = ∑ i, d i * x i * y i := by
-- proof
  simp [dotProduct, Matrix.vecMul, Matrix.diagonal]
  apply Finset.sum_congr rfl
  ring_nf
  simp


-- created on 2026-09-19
