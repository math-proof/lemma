import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c : ℤ}
-- given
  (hac : a ≤ c)
  (hcb : c ≤ b) :
-- imply
  Set.Icc a b = Set.Ico a c ∪ Set.Icc c b := by
-- proof
  ext x
  simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ico]
  constructor
  · rintro ⟨hax, hxb⟩
    by_cases h : x < c
    · exact Or.inl ⟨hax, h⟩
    · exact Or.inr ⟨by omega, hxb⟩
  · rintro (h | h)
    · exact ⟨h.1, by omega⟩
    · exact ⟨by omega, h.2⟩


-- created on 2023-04-18
