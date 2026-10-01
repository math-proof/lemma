import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {y : β}
  {f : α → β}
-- given
  (h : ∃ x ∈ S, y = f x) :
-- imply
  y ∈ f '' S := by
-- proof
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩


-- created on 2020-07-30
