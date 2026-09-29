import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a : ℝ}
-- given
  (h : a ≠ 0) :
-- imply
  a ^ 2 > 0 := by
-- proof
  exact lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 h))


-- created on 2026-09-27
