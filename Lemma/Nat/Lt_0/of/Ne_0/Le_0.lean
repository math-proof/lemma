import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≠ 0)
  (h₁ : x ≤ 0) :
-- imply
  x < 0 := by
-- proof
  exact lt_of_le_of_ne h₁ h₀


-- created on 2026-09-27
