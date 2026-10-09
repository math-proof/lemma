import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∉ Set.Iio a) :
-- imply
  a ≤ x := by
-- proof
  exact not_lt.mp h


-- created on 2021-09-21
