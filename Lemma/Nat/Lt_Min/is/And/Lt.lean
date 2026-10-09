import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y z : α} :
-- imply
  x < min y z ↔ x < y ∧ x < z := by
-- proof
  exact lt_min_iff


-- created on 2022-01-01
