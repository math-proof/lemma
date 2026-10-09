import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c : ℤ} :
-- imply
  Finset.Ico a (max b c) = Finset.Ico a b ∪ Finset.Ico a c := by
-- proof
  ext x
  simp only [Finset.mem_Ico, Finset.mem_union, lt_max_iff]
  constructor
  · rintro ⟨ha, h | h⟩
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, h⟩
  · rintro (⟨ha, h⟩ | ⟨ha, h⟩)
    · exact ⟨ha, Or.inl h⟩
    · exact ⟨ha, Or.inr h⟩


-- created on 2022-01-08
