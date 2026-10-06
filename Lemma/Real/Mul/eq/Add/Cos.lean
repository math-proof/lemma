import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos x * Real.cos y = (Real.cos (x + y) + Real.cos (x - y)) / 2 := by
-- proof
  grind [Real.cos_add, Real.cos_sub]


-- created on 2023-06-01
