import sympy.Basic
import Mathlib.Data.Matrix.Mul
open scoped Matrix


@[main, comm]
private lemma main
  {m n β : Type*} [Fintype m]
  {s : Finset β}
-- given
  (f : β → m → ℝ)
  (A : Matrix m n ℝ) :
-- imply
  (∑ x ∈ s, f x) ᵥ* A = ∑ x ∈ s, (f x) ᵥ* A := by
-- proof
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]


-- created on 2026-09-19
