import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : a < b) :
-- imply
  a / x < b / x :=
-- proof
  (div_lt_div_iff_of_pos_right h₀).mpr h₁


-- created on 2019-06-27
