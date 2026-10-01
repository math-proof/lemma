import Mathlib.LinearAlgebra.Matrix.ZPow
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (_h : k > 0) :
-- imply
  (A ^ (-(k : ℤ))).det = A.det ^ (-(k : ℤ)) := by
-- proof
  rw [Matrix.zpow_neg_natCast, Matrix.det_nonsing_inv, Matrix.det_pow, Ring.inverse_eq_inv, zpow_neg, zpow_natCast]


-- created on 2026-09-27
