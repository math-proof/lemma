import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  x ≥ y ↔ x - y ≥ 0 := by
-- proof
  exact sub_nonneg.symm


-- created on 2023-04-18
