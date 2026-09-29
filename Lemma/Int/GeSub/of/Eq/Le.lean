import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x = y)
  (h₁ : a ≤ b) :
-- imply
  x - a ≥ y - b := by
-- proof
  linarith


-- created on 2026-09-27
