import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∉ Set.Ici a) :
-- imply
  x < a :=
-- proof
  not_le.mp h


-- created on 2021-08-31
