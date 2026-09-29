import sympy.Basic


@[main]
private lemma given
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x > y ∨ x > z) :
-- imply
  x > min y z :=
-- proof
  min_lt_iff.mpr h


-- created on 2026-09-27
