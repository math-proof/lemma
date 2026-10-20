import sympy.Basic


@[path]
private lemma main
  {f g : ι → Set α} :
-- imply
  Set.iUnion (fun i => f i ∪ g i) = Set.iUnion f ∪ Set.iUnion g := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  ·
    rintro ⟨i, hx | hx⟩
    ·
      exact Or.inl ⟨i, hx⟩
    ·
      exact Or.inr ⟨i, hx⟩
  ·
    rintro (⟨i, hx⟩ | ⟨i, hx⟩)
    ·
      exact ⟨i, Or.inl hx⟩
    ·
      exact ⟨i, Or.inr hx⟩


-- created on 2021-02-10
-- updated on 2026-10-17
