import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a < b)
  (h₁ : x < y) :
-- imply
  a + x < b + y := by
-- proof
  exact add_lt_add h₀ h₁


-- created on 2026-09-27
