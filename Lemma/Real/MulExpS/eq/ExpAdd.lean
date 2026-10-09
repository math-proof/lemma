import sympy.Basic


@[path]
private lemma main
-- given
  (a b : ℝ) :
-- imply
  Real.exp a * Real.exp b = Real.exp (a + b) := by
-- proof
  grind [Real.exp_add]


-- created on 2018-10-25
