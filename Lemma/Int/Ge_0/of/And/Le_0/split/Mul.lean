import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y : ℝ}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≤ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  nlinarith


-- created on 2023-04-15
