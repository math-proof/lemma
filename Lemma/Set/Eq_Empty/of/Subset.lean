import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A \ B = ∅ :=
-- proof
  Set.sdiff_eq_empty.mpr h


-- created on 2021-05-04
