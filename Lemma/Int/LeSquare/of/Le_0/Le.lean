import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x M : ℝ}
-- given
  (h₀ : x ≤ 0)
  (h₁ : M ≤ x) :
-- imply
  x * x ≤ M * M := by
-- proof
  nlinarith


-- created on 2026-09-27
