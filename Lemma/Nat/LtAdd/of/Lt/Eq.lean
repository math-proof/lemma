import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : b < y)
  (h₁ : a = x) :
-- imply
  a + b < x + y := by
-- proof
  linarith


-- created on 2026-09-27
