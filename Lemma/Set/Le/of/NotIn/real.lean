import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∉ Set.Ioi a) :
-- imply
  x ≤ a := by
-- proof
  simp only [Set.mem_Ioi, not_lt] at h
  exact h


-- created on 2021-08-20
