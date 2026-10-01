import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  |x - y| = |y - x| := by
-- proof
  exact abs_sub_comm x y


-- created on 2026-09-27
