import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x ≤ max x y := by
-- proof
  exact le_max_left x y


-- created on 2023-04-23
