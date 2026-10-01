import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ ({0}ᶜ : Set ℝ)) :
-- imply
  |x| ∈ Set.Ioi 0 := by
-- proof
  exact Set.mem_Ioi.mpr (abs_pos.mpr (Set.mem_compl_singleton_iff.mp h))


-- created on 2020-04-16
