import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  |x| ≤ |x - y| + |y| := by
-- proof
  simpa using abs_add_le (x - y) y


-- created on 2019-07-26
