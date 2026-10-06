import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : 0 < x) :
-- imply
  x ∈ Set.Ioi 0 := by
-- proof
  exact h


-- created on 2020-04-25
