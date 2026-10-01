import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h₀ : x ≤ y)
  (h₁ : x ≠ y) :
-- imply
  x < y := by
-- proof
  exact lt_of_le_of_ne h₀ h₁


-- created on 2023-11-12
