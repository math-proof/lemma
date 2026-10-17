import sympy.Basic


@[path]
private lemma main
  {A B X Y : Set α}
-- given
  (h₀ : A ⊇ B)
  (h₁ : X ⊇ Y) :
-- imply
  A ∪ X ⊇ B ∪ Y :=
-- proof
  Set.union_subset_union h₀ h₁


-- created on 2021-06-28
-- updated on 2026-10-17
