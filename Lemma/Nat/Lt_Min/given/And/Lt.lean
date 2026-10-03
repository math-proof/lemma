import sympy.Basic


@[main]
private lemma main
  {x y z : ℤ}
-- given
  (h₀ : x < y)
  (h₁ : x < z) :
-- imply
  x < min y z := by
-- proof
  exact lt_min h₀ h₁


-- created on 2022-01-01
