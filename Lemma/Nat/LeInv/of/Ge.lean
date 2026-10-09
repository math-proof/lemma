import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (ha : a > 0)
  (h : x ≥ a) :
-- imply
  1 / x ≤ 1 / a := by
-- proof
  exact one_div_le_one_div_of_le ha h


-- created on 2019-06-02
