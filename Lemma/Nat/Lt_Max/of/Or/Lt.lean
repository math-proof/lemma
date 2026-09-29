import sympy.Basic


@[main]
private lemma given
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x < y ∨ x < z) :
-- imply
  x < max y z :=
-- proof
  lt_max_iff.mpr h


-- created on 2026-09-27
