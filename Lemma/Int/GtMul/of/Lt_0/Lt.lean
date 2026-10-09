import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : a < b) :
-- imply
  a * x > b * x :=
-- proof
  mul_lt_mul_of_neg_right h₁ h₀


-- created on 2019-07-14
