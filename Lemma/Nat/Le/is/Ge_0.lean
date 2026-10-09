import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  x ≤ y ↔ y - x ≥ 0 := by
-- proof
  exact sub_nonneg.symm


-- created on 2023-06-19
