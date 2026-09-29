import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (_h₀ : x < 0)
  (h₁ : a = b) :
-- imply
  a / x = b / x := by
-- proof
  rw [h₁]


-- created on 2026-09-27
