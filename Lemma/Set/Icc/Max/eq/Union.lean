import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c : ℤ} :
-- imply
  Set.Ioo a (max b c) = Set.Ioo a b ∪ Set.Ioo a c := by
-- proof
  ext x
  simp only [Set.mem_Ioo, Set.mem_union, lt_max_iff]
  constructor
  · rintro ⟨ha, h | h⟩
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, h⟩
  · rintro (⟨ha, h⟩ | ⟨ha, h⟩)
    · exact ⟨ha, Or.inl h⟩
    · exact ⟨ha, Or.inr h⟩


-- created on 2022-01-08
