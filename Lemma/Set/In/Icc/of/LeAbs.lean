import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| ≤ a) :
-- imply
  x ∈ Icc (-a) a := by
-- proof
  exact Set.mem_Icc.mpr (abs_le.mp h)


-- created on 2021-01-07
