import sympy.Basic


@[main]
private lemma main
  {s : Set α}
  {f : α → β} :
-- imply
  ∀ e ∈ f '' s, ∃ x ∈ s, f x = e := by
-- proof
  intro e h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩


-- created on 2026-09-27
