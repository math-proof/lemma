import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  x > y ∨ x = y :=
-- proof
  (lt_or_eq_of_le h).imp id Eq.symm


-- created on 2026-09-27
