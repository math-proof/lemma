import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∉ Set.Iic a) :
-- imply
  a < x := by
-- proof
  exact not_le.mp h


-- created on 2021-08-27
