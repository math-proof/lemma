import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ} :
-- imply
  min (a + c) (b + c) = c + min a b := by
-- proof
  rw [min_add_add_right, add_comm]


-- created on 2019-05-13
