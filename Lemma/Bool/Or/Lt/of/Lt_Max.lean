import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x < max y z) :
-- imply
  x < y ∨ x < z :=
-- proof
  lt_max_iff.mp h


-- created on 2026-09-27
