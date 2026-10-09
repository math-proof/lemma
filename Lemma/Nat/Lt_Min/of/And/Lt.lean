import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x < y ∧ x < z) :
-- imply
  x < min y z :=
-- proof
  lt_min h.1 h.2


-- created on 2022-01-01
