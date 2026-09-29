import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  |x| ≤ |x - y| + |y| := by
-- proof
  simpa using abs_add_le (x - y) y


-- created on 2026-09-27
