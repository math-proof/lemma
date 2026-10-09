import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  |x| + |y| ≥ |x + y| := by
-- proof
  exact abs_add_le x y


-- created on 2023-06-03
