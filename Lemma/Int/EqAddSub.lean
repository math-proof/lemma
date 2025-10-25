import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a - b + b = a := by
-- proof
  rw [sub_add_cancel]


-- created on 2024-07-01
