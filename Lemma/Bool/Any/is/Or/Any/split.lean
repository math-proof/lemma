import sympy.Basic


@[main]
private lemma main
  {d : ℝ}
  {f : ℝ → Prop}
-- given
  (hd : 0 < d) :
-- imply
  (∃ x ∈ Set.Ioo (-d) d, f x) ↔ (∃ x ∈ Set.Ioo (-d) 0, f x) ∨ ∃ x ∈ Set.Ico 0 d, f x := by
-- proof
  constructor
  · rintro ⟨x, hx, hfx⟩
    simp only [Set.mem_Ioo] at hx
    by_cases h : x < 0
    · exact Or.inl ⟨x, ⟨hx.1, h⟩, hfx⟩
    · exact Or.inr ⟨x, ⟨by linarith, hx.2⟩, hfx⟩
  · rintro (⟨x, hx, hfx⟩ | ⟨x, hx, hfx⟩)
    · simp only [Set.mem_Ioo] at hx
      exact ⟨x, ⟨hx.1, by linarith⟩, hfx⟩
    · simp only [Set.mem_Ico] at hx
      exact ⟨x, ⟨by linarith [hx.1], hx.2⟩, hfx⟩


-- created on 2023-10-22
