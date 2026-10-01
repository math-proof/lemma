import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  b > a := by
-- proof
  exact lt_of_le_of_lt h₀ h₁


-- created on 2026-09-27
