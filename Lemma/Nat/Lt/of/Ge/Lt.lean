import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b : ℝ}
-- given
  (h₀ : x ≥ b)
  (h₁ : x < a) :
-- imply
  b < a := by
-- proof
  exact lt_of_le_of_lt h₀ h₁


-- created on 2026-09-27
