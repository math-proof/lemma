import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioi 0) :
-- imply
  1 / x ∈ Set.Ioi 0 := by
-- proof
  rw [Set.mem_Ioi] at *
  exact one_div_pos.mpr h


-- created on 2020-04-14
