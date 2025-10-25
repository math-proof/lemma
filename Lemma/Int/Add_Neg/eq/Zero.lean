import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  {a : α} :
-- imply
  a + -a = 0 := by
-- proof
  apply add_neg_cancel


-- created on 2024-11-25
