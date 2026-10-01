import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : min y z ≤ x) :
-- imply
  y ≤ x ∨ z ≤ x :=
-- proof
  min_le_iff.mp h


-- created on 2026-09-27
