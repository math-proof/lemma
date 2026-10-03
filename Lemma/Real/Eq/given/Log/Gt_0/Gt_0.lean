import sympy.functions.elementary.exponential


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : 0 < x)
  (h₁ : 0 < y)
  (h : x = y) :
-- imply
  Real.log x = Real.log y := by
-- proof
  rw [h]


-- created on 2026-10-03
