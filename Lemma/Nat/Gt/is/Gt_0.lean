import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x > y ↔ x - y > 0 := by
-- proof
  exact sub_pos.symm


-- created on 2026-09-27
