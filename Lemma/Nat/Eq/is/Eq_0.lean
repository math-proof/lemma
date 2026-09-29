import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a = b ↔ a - b = 0 :=
-- proof
  sub_eq_zero.symm


-- created on 2026-09-27
