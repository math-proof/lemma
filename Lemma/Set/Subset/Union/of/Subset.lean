import sympy.Basic


@[path]
private lemma main
  {A B S : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A ∪ S ⊆ B ∪ S :=
-- proof
  Set.union_subset_union h fun _ hx ↦ hx


-- created on 2020-07-19
