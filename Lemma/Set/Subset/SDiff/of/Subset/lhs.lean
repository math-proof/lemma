import sympy.Basic


@[path]
private lemma main
  {A B S : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A \ S ⊆ B :=
-- proof
  Set.sdiff_subset.trans h


-- created on 2021-06-27
