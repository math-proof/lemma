import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.sin x * Real.cos y - Real.cos x * Real.sin y = Real.sin (x - y) := by
-- proof
  grind [Real.sin_sub]


-- created on 2023-06-01
