import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : y > 0) :
-- imply
  x / y > 0 := by
-- proof
  exact div_pos h₀ h₁


-- created on 2026-09-27
