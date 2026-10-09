import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∈ Set.Ioo (-a) a) :
-- imply
  |x| < a :=
-- proof
  abs_lt.mpr h


-- created on 2021-03-12
