import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a ≥ x)
  (h₁ : y > b) :
-- imply
  a + y > x + b :=
-- proof
  add_lt_add_of_le_of_lt h₀ h₁


-- created on 2026-10-01
