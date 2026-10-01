import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  |x| = if x > 0 then x else if x = 0 then 0 else -x := by
-- proof
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h, if_neg (not_lt.mpr h.le), if_neg h.ne]
  · rw [h, abs_zero, if_neg (lt_irrefl 0), if_pos rfl]
  · rw [abs_of_pos h, if_pos h]


-- created on 2018-02-12
