import sympy.Basic


@[path]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a = b ↔ a - b = 0 :=
-- proof
  sub_eq_zero.symm


-- created on 2021-12-29
