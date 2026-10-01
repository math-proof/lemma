import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given.relax
  {x b : ℤ}
-- given
  (h₀ : x ≤ b)
  (h : x ≥ b) :
-- imply
  x = b := by
-- proof
  exact le_antisymm h₀ h


-- created on 2019-03-31
