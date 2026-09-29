import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x ≤ a)
  (h₁ : y ≥ b) :
-- imply
  (x - a) * (y - b) ≤ 0 := by
-- proof
  nlinarith


-- created on 2026-09-27
