import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (hge : b ≤ a)
  (hneg : c < 0)
  -- imply
  : a / c ≤ b / c := by
  -- proof
  have hnc : 0 < -c := by linarith
  have hnum : 0 ≤ a - b := by linarith
  have hdiv : 0 ≤ (a - b) / (-c) := div_nonneg hnum (le_of_lt hnc)
  have heq : (a - b) / (-c) = (b - a) / c := by
    field_simp
    <;> ring
  have hdiff : 0 ≤ (b - a) / c := by
    rw [← heq]
    exact hdiv
  have h : b / c - a / c = (b - a) / c := by
    field_simp
  linarith

-- created on 2023-03-26
