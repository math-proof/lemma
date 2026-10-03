import sympy.functions.elementary.exponential


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.exp x = Real.exp y := by
-- proof
  rw [h]


-- created on 2026-10-03
