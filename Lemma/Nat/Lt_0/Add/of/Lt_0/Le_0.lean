import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a y : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : y ≤ 0) :
-- imply
  a + y < 0 := by
-- proof
  linarith


-- created on 2026-09-27
