import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ} :
-- imply
  |x * y - a * b| ≤ |a| * |y - b| + |x - a| * |y| := by
-- proof
  have e : x * y - a * b = a * (y - b) + (x - a) * y := by ring
  rw [e, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _


-- created on 2019-10-01
