import sympy.Basic


@[path]
private lemma main
  {x y z : ℝ}
-- given
  (h₀ : x ≥ z)
  (h₁ : z > y) :
-- imply
  x > y := by
-- proof
  exact lt_of_lt_of_le h₁ h₀


-- created on 2019-07-01
