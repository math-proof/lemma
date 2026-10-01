import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x ≤ a)
  (h₁ : x ≤ b) :
-- imply
  x ≤ min a b := by
-- proof
  exact le_min h₀ h₁


-- created on 2026-09-27
