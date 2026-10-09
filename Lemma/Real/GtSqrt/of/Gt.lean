import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hy : 0 ≤ y)
  (h : x > y) :
-- imply
  Real.sqrt x > Real.sqrt y := by
-- proof
  exact Real.sqrt_lt_sqrt hy h


-- created on 2019-07-01
