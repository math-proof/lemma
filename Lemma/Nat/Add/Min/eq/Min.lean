import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y z w : ℝ} :
-- imply
  min x y + min z w = min (min (x + z) (x + w)) (min (y + z) (y + w)) := by
-- proof
  rw [← min_add_add_right, ← min_add_add_left, ← min_add_add_left]


-- created on 2026-09-27
