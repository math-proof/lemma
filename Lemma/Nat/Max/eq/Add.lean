import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y r : ℝ} :
-- imply
  max (x * r + 1) (y * r + 1) = 1 + max (x * r) (y * r) := by
-- proof
  rw [max_add_add_right, add_comm]


-- created on 2019-03-10
