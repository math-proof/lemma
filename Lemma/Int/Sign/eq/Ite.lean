import Mathlib.Basic.Real.Sign
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sign x = if x > 0 then 1 else if x < 0 then -1 else 0 := by
-- proof
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]
  · rw [h, Real.sign_zero, ite_eq_right (lt_irrefl 0), ite_eq_right (lt_irrefl 0)]
  · rw [Real.sign_of_pos h, ite_eq_left h]


-- created on 2023-10-22
