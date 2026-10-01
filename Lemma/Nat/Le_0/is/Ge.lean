import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x - y ≤ 0 ↔ y ≥ x := by
-- proof
  exact sub_nonpos


-- created on 2023-06-20
