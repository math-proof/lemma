import Lemma.Basic


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  (A ∪ B) ∩ A = A := by
-- proof
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨ha | hb, ha'⟩
    · exact ha'
    · exact ha'
  · intro ha
    exact ⟨Or.inl ha, ha⟩



-- created on 2025-07-20
