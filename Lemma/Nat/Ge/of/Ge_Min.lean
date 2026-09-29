import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : min a b ≥ x) :
-- imply
  a ≥ x := by
-- proof
  exact le_trans h (min_le_left a b)


-- created on 2026-09-27
