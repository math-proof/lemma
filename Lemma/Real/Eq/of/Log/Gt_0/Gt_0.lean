import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  -- given
  (h₀ : x > 0)
  (h₁ : y > 0)
  (h₂ : x.log = y.log) :
-- imply
  x = y := by
-- proof
  rw [← Real.exp_log h₀]
  rw [← Real.exp_log h₁]
  rw [h₂]


-- created on 2025-10-03
