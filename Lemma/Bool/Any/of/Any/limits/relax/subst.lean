import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
  {p : ℝ → Prop}
-- given
  (h₀ : ∃ x ∈ Set.Ico a b, p x) :
-- imply
  ∃ x ∈ Set.Icc a b, p x := by
-- proof
  obtain ⟨x, hx, hp⟩ := h₀
  exact ⟨x, ⟨hx.1, le_of_lt hx.2⟩, hp⟩


-- created on 2019-02-16
-- updated on 2026-10-26
