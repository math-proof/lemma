import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y)
  (m : ℝ) :
-- imply
  min x m ≥ min y m := by
-- proof
  exact min_le_min h le_rfl


-- created on 2019-05-28
