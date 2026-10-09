import sympy.Basic


@[path]
private lemma binary
  [Decidable c]
  {p f g : α}
-- given
  (h : p = if c then f else g) :
-- imply
  c ∧ p = f ∨ ¬c ∧ p = g := by
-- proof
  by_cases hc : c
  ·
    left
    exact ⟨hc, by rw [h, if_pos hc]⟩
  ·
    right
    exact ⟨hc, by rw [h, if_neg hc]⟩


-- created on 2018-01-07
