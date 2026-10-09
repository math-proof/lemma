import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  x - y ≥ 0 ↔ y ≤ x := by
-- proof
  exact sub_nonneg


-- created on 2023-06-20
