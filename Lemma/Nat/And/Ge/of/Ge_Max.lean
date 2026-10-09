import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x ≥ max y z) :
-- imply
  x ≥ y ∧ x ≥ z :=
-- proof
  max_le_iff.mp h


-- created on 2019-06-06
