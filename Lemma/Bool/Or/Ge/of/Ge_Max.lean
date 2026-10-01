import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : max y z ≥ x) :
-- imply
  y ≥ x ∨ z ≥ x :=
-- proof
  le_max_iff.mp h


-- created on 2022-01-02
