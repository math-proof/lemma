import sympy.Basic


@[path]
private lemma main
  {a b c d : ℝ} :
-- imply
  (a / 2 + b / 2 - c) * d = (a + b - 2 * c) * d / 2 := by
-- proof
  field_simp


-- created on 2023-06-03
