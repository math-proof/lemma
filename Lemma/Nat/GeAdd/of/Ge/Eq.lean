import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : y ≥ b)
  (h₁ : a = x) :
-- imply
  a + y ≥ x + b := by
-- proof
  linarith


-- created on 2026-09-27
