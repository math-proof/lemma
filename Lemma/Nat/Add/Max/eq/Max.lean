import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y z w : ℝ} :
-- imply
  max x y + max z w = max (max (x + z) (x + w)) (max (y + z) (y + w)) := by
-- proof
  rw [← max_add_add_right, ← max_add_add_left, ← max_add_add_left]


-- created on 2026-09-27
