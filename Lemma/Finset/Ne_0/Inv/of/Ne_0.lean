import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h : A.det ≠ 0) :
-- imply
  A⁻¹.det ≠ 0 := by
-- proof
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero h


-- created on 2023-05-01
