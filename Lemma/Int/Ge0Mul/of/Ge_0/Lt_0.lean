import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y < 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  nlinarith


-- created on 2019-07-03
