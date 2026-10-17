import sympy.Basic


@[path]
private lemma main
  {A B S : Set α}
-- given
  (h₀ : B ⊆ A) :
-- imply
  B ∪ S ⊆ A ∪ S :=
-- proof
  Set.union_subset_union h₀ subset_rfl


-- created on 2026-10-11
-- updated on 2026-10-17
