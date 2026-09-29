import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioi 0) :
-- imply
  |x| ∈ Set.Ioi 0 := by
-- proof
  exact Set.mem_Ioi.mpr (abs_pos.mpr (ne_of_gt (Set.mem_Ioi.mp h)))


-- created on 2026-09-27
