import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  |x| = if x > 0 then x else if x = 0 then 0 else -x := by
-- proof
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h, ite_eq_right (not_lt.mpr h.le), ite_eq_right h.ne]
  · rw [h, abs_zero, ite_eq_right (lt_irrefl 0), ite_eq_left rfl]
  · rw [abs_of_pos h, ite_eq_left h]


-- created on 2018-02-12
