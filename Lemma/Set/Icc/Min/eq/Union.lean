import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℤ} :
-- imply
  Set.Ico (min b c) a = Set.Ico b a ∪ Set.Ico c a := by
-- proof
  ext x
  simp only [Set.mem_Ico, Set.mem_union, min_le_iff]
  constructor
  · rintro ⟨h | h, ha⟩
    · exact Or.inl ⟨h, ha⟩
    · exact Or.inr ⟨h, ha⟩
  · rintro (⟨h, ha⟩ | ⟨h, ha⟩)
    · exact ⟨Or.inl h, ha⟩
    · exact ⟨Or.inr h, ha⟩


-- created on 2022-01-08
