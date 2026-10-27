import Initialize.Tactic.Attr.Basic


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
    exact ⟨hc, by rw [h, ite_eq_left hc]⟩
  ·
    right
    exact ⟨hc, by rw [h, ite_eq_right hc]⟩


-- created on 2018-01-07
