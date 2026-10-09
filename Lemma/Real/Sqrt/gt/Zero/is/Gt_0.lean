import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : 0 < Real.sqrt x) :
-- imply
  0 < x := by
-- proof
  exact Real.sqrt_pos.mp h


-- created on 2023-06-20
