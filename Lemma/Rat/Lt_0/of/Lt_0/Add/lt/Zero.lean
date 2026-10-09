import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c x : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : b ^ 2 - a * c * 4 < 0) :
-- imply
  a * x ^ 2 + b * x + c < 0 := by
-- proof
  nlinarith [sq_nonneg (2 * a * x + b)]


-- created on 2022-04-02
