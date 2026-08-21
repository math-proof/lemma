import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
-- proof
  grind [Real.cos_add]


-- created on 2018-06-15
-- updated on 2023-11-26
