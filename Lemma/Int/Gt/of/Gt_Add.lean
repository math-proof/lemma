import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ}
-- given
  (h₀ : x > z)
  (h₁ : z ≥ y) :
-- imply
  x > y :=
-- proof
  lt_of_le_of_lt h₁ h₀


-- created on 2026-10-01
