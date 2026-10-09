import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≤ 0)
  (h : x ≥ 0) :
-- imply
  x = 0 := by
-- proof
  exact le_antisymm h₀ h


-- created on 2019-06-16
