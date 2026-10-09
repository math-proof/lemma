import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : y ≤ 0) :
-- imply
  x < 0 := by
-- proof
  linarith


-- created on 2020-05-14
