import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y : ℝ}
-- given
  (h : y ≤ x) :
-- imply
  x = max x y := by
-- proof
  exact (max_eq_left h).symm


-- created on 2023-04-23
