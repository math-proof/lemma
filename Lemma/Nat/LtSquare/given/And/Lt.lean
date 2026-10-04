import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ^ 2 < a) :
-- imply
  x < Real.sqrt a ∧ -Real.sqrt a < x := by
-- proof
  have hx : |x| < Real.sqrt a := (Real.lt_sqrt (abs_nonneg x)).mpr (by rwa [sq_abs])
  rw [abs_lt] at hx
  exact ⟨hx.2, hx.1⟩


-- created on 2020-01-15
-- updated on 2023-06-18
