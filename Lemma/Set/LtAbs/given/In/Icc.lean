import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| < a) :
-- imply
  x ∈ Set.Ioo (-a) a := by
-- proof
  apply Set.mem_Ioo.mpr (abs_lt.mp h)


-- created on 2020-04-24
