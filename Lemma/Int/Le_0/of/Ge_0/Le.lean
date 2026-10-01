import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x ≤ a) :
-- imply
  x * (x - a) ≤ 0 := by
-- proof
  nlinarith


-- created on 2019-06-21
