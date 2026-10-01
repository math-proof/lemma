import Mathlib.LinearAlgebra.Matrix.ZPow
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) ℝ}
  {t : ℝ}
-- given
  (h : t ≠ 0) :
-- imply
  (t • A - t • B) ^ (-2 : ℤ) = t ^ (-2 : ℤ) • (A - B) ^ (-2 : ℤ) := by
-- proof
  rw [← smul_sub]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 h
  show (t • (A - B)) ^ (-((2 : ℕ) : ℤ)) = t ^ (-((2 : ℕ) : ℤ)) • (A - B) ^ (-((2 : ℕ) : ℤ))
  rw [Matrix.zpow_neg_natCast, Matrix.zpow_neg_natCast, zpow_neg, zpow_natCast, smul_pow]
  by_cases hu : IsUnit ((A - B) ^ 2).det
  · have : Invertible (t ^ 2) := invertibleOfNonzero ht2
    rw [Matrix.inv_smul (k := t ^ 2) (h := hu), invOf_eq_inv]
  · have hu' : ¬ IsUnit (t ^ 2 • (A - B) ^ 2).det := by
      rw [Matrix.det_smul]
      exact fun hh => hu (isUnit_of_mul_isUnit_right hh)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu', smul_zero]


-- created on 2026-09-27
