import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  x ∈ Set.Ioi 0 := by
-- proof
  exact Set.mem_Ioi.mpr h


-- created on 2026-09-27
