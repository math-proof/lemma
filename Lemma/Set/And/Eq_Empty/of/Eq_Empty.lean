import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∪ B = ∅) :
-- imply
  A = ∅ ∧ B = ∅ := by
-- proof
  have ha : A ⊆ (∅ : Set α) := by
    rw [←h]
    exact Set.subset_union_left (s := A) (t := B)
  have hb : B ⊆ (∅ : Set α) := by
    rw [←h]
    exact Set.subset_union_right (s := A) (t := B)
  exact ⟨Set.eq_empty_of_subset_empty ha, Set.eq_empty_of_subset_empty hb⟩


-- created on 2021-05-13
