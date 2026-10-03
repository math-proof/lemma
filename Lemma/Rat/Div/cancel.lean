import sympy.Basic


@[main]
private lemma main
  {a b c d : ℝ}
-- given
  (hc : c ≠ 0)
  (hd : d ≠ 0) :
-- imply
  (a + 1 / c) / (b + 1 / d) = (a * c * d + d) / (b * c * d + c) := by
-- proof
  field_simp


-- created on 2020-06-29
-- updated on 2023-04-05
