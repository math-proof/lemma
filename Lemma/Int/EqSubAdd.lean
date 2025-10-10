import sympy.Basic


@[main]
private lemma left
  [AddCommGroup α]
  {a b : α} :
-- imply
  a + b - a = b := by
-- proof
  apply add_sub_cancel_left


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a + b - b = a := by
-- proof
  apply add_sub_cancel_right


-- created on 2025-10-10
