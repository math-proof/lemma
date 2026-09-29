import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioi 0) :
-- imply
  √x ∈ Set.Ioi 0 :=
-- proof
  Set.mem_Ioi.mpr (Real.sqrt_pos.mpr h)


-- created on 2026-09-27
