import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : a * x ≤ b * x) :
-- imply
  a ≤ b := by
-- proof
  nlinarith


-- created on 2023-10-03
