import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a > x)
  (h₁ : b ≥ y) :
-- imply
  a + b ≥ x + y := by
-- proof
  linarith


-- created on 2019-07-12
