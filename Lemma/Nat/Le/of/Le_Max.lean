import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : max a b ≤ x) :
-- imply
  a ≤ x := by
-- proof
  exact le_trans (le_max_left a b) h


-- created on 2019-11-29
