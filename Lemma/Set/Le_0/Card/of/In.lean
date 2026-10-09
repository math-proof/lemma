import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.univ \ {0}) :
-- imply
  0 < |x| := by
-- proof
  apply abs_pos.mpr (Set.mem_sdiff_singleton.mp h).2


-- created on 2021-03-11
