import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x b : ℤ}
-- given
  (h₀ : x ≥ b)
  (h : x ≤ b) :
-- imply
  x = b := by
-- proof
  exact le_antisymm h h₀


-- created on 2026-09-27
