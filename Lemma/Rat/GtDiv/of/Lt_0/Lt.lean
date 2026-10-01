import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : a < b) :
-- imply
  a / x > b / x := by
-- proof
  have h₂ : b / x - a / x = (b - a) / x := by ring
  have h₃ : (b - a) / x < 0 := div_neg_of_pos_of_neg (by linarith) h₀
  linarith


-- created on 2019-07-15
