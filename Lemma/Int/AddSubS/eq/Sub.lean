import sympy.Basic


@[main]
private lemma main
  [AddGroup G]
-- given
  (a b c : G) :
-- imply
  a - b + (b - c) = a - c :=
-- proof
  sub_add_sub_cancel a b c


-- created on 2025-12-08
