import sympy.Basic


@[path]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a - b = 0 :=
-- proof
  sub_eq_zero.mpr h


-- created on 2020-10-16
