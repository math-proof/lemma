import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x > y ↔ y - x < 0 := by
-- proof
  exact sub_neg.symm


-- created on 2026-09-27
