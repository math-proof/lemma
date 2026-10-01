import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  |x| = if x ≤ 0 then -x else x := by
-- proof
  split_ifs with h
  · exact abs_of_nonpos h
  · exact abs_of_nonneg (le_of_lt (not_le.mp h))


-- created on 2026-09-27
