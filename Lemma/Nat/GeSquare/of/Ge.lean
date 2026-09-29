import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : y ≥ 0)
  (h : x ≥ y) :
-- imply
  x * x ≥ y * y := by
-- proof
  nlinarith


-- created on 2026-09-27
