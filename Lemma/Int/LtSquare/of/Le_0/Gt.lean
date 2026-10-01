import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x m : ℝ}
-- given
  (h₀ : x ≤ 0)
  (h₁ : x > m) :
-- imply
  x * x < m * m := by
-- proof
  nlinarith


-- created on 2026-09-27
