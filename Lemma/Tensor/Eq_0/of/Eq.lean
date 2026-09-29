import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a - b = 0 :=
-- proof
  sub_eq_zero.mpr h


-- created on 2026-09-27
