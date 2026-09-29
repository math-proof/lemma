import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a > x)
  (h₁ : y ≥ b) :
-- imply
  a + y > x + b := by
-- proof
  linarith


-- created on 2026-09-27
