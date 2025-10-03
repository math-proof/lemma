import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
   (h₀ : x ≠ 0)
   (h₁ : y ≠ 0) :
-- imply
  (x * y).log = x.log + y.log := 
-- proof
  Real.log_mul h₀ h₁


-- created on 2025-10-03
