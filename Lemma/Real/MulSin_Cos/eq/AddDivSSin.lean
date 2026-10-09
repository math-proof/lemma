import sympy.Basic


@[path]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.sin x * Real.cos y = (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
-- proof
  grind [Real.sin_add, Real.sin_sub]


-- created on 2020-12-02
-- updated on 2023-06-01
