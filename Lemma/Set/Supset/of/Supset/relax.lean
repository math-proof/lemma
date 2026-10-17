import sympy.Basic


@[path]
private lemma main
  {A B S : Set α}
-- given
  (h : A ⊇ B) :
-- imply
  A ∪ S ⊇ B :=
-- proof
  subset_trans h Set.subset_union_left


-- created on 2021-06-28
-- updated on 2026-10-17
