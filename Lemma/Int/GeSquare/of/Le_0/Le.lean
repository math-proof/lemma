import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≤ x) :
-- imply
  y ^ 2 ≥ x ^ 2 := by
-- proof
  nlinarith


-- created on 2026-09-27
