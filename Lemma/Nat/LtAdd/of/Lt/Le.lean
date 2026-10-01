import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : y ≤ b) :
-- imply
  a + y < x + b :=
-- proof
  add_lt_add_of_lt_of_le h₀ h₁


-- created on 2018-11-29
