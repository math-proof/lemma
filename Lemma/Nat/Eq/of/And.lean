import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given.squeeze
  {x y : ℝ}
-- given
  (h₀ : x ≤ y)
  (h₁ : x ≥ y) :
-- imply
  x = y := by
-- proof
  exact le_antisymm h₀ h₁


-- created on 2019-03-30
