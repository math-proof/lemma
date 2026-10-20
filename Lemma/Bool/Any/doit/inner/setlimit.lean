import sympy.Basic


@[path]
private lemma main
  {m a b c d : ℤ}
  {p : ℤ → ℤ → Prop} :
-- imply
  (∃ j ∈ ({a, b, c, d} : Set ℤ), ∃ i ∈ Set.Ico 0 m, p i j) ↔
    ∃ i ∈ Set.Ico 0 m, p i a ∨ p i b ∨ p i c ∨ p i d := by
-- proof
  constructor
  ·
    intro h
    obtain ⟨j, hj, i, hi, hp⟩ := h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    obtain rfl | rfl | rfl | rfl := hj
    · exact ⟨i, hi, Or.inl hp⟩
    · exact ⟨i, hi, Or.inr <| Or.inl hp⟩
    · exact ⟨i, hi, Or.inr <| Or.inr <| Or.inl hp⟩
    · exact ⟨i, hi, Or.inr <| Or.inr <| Or.inr hp⟩
  ·
    intro h
    obtain ⟨i, hi, hp⟩ := h
    obtain hp | hp | hp | hp := hp
    · exact ⟨a, by simp, i, hi, hp⟩
    · exact ⟨b, by simp, i, hi, hp⟩
    · exact ⟨c, by simp, i, hi, hp⟩
    · exact ⟨d, by simp, i, hi, hp⟩


-- created on 2019-02-10
-- updated on 2026-10-17
