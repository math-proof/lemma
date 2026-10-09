import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  |x - y| = |y - x| := by
-- proof
  exact abs_sub_comm x y


-- created on 2018-01-19
