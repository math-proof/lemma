import sympy.Basic


@[main]
private lemma main
  {a b c d x : ℝ}
-- given
  (h₀ : c ≠ 0)
  (h₁ : a * x + b = (a + c) * x + d) :
-- imply
  x = (b - d) / c := by
-- proof
  field_simp
  linarith


-- created on 2020-06-29
