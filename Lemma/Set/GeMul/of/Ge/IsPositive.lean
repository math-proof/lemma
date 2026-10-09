import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : b ≤ a)
  (hx : 0 < x) :
-- imply
  b * x ≤ a * x := by
-- proof
  exact mul_le_mul_of_nonneg_right h hx.le


-- created on 2021-10-02
-- updated on 2023-05-14
