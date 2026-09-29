import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x - y ≥ 0 ↔ y ≤ x := by
-- proof
  exact sub_nonneg


-- created on 2026-09-27
