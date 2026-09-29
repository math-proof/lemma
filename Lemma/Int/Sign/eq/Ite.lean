import Mathlib.Data.Real.Sign
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  Real.sign x = if x > 0 then 1 else if x < 0 then -1 else 0 := by
-- proof
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, if_neg (not_lt.mpr h.le), if_pos h]
  · rw [h, Real.sign_zero, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
  · rw [Real.sign_of_pos h, if_pos h]


-- created on 2026-09-27
