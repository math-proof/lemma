import sympy.Basic


@[path]
private lemma main
  [Decidable a] [Decidable b]
  {e f g k : β → α}
-- given
  (h : (a → ∃ x, e x = f x) ∧ (¬a ∧ b → ∃ x, e x = g x) ∧ (¬a ∧ ¬b → ∃ x, e x = k x)) :
-- imply
  ∃ x, e x = if a then f x else if b then g x else k x := by
-- proof
  by_cases ha : a
  ·
    obtain ⟨x, hx⟩ := h.1 ha
    exact ⟨x, by rw [if_pos ha]; exact hx⟩
  ·
    by_cases hb : b
    ·
      obtain ⟨x, hx⟩ := h.2.1 ⟨ha, hb⟩
      exact ⟨x, by rw [if_neg ha, if_pos hb]; exact hx⟩
    ·
      obtain ⟨x, hx⟩ := h.2.2 ⟨ha, hb⟩
      exact ⟨x, by rw [if_neg ha, if_neg hb]; exact hx⟩


-- created on 2023-07-01
