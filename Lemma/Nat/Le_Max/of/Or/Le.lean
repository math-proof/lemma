import sympy.Basic


@[main]
private lemma given
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x ≤ y ∨ x ≤ z) :
-- imply
  x ≤ max y z :=
-- proof
  le_max_iff.mpr h


-- created on 2022-01-02
