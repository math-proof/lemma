import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
-- proof
  grind [Real.cos_sub]


-- created on 2026-08-01
