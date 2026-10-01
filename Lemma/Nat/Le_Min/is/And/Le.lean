import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α} :
-- imply
  x ≤ min y z ↔ x ≤ y ∧ x ≤ z :=
-- proof
  le_min_iff


-- created on 2026-09-27
