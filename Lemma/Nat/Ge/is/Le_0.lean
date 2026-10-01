import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x ≥ y ↔ y - x ≤ 0 := by
-- proof
  exact sub_nonpos.symm


-- created on 2023-06-19
