import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {f : α → β}
  {y : β}
-- given
  (h : y ∈ f '' S) :
-- imply
  ∃ x ∈ S, y = f x := by
-- proof
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩


-- created on 2026-09-27
