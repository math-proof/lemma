import sympy.Basic


@[path]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.sin x * Real.sin y = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
-- proof
  grind [Real.cos_add, Real.cos_sub]


-- created on 2020-12-03
