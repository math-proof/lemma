import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : (∃ x ∈ A, f x) ∨ ∃ x ∈ A, g x) :
-- imply
  ∃ x ∈ A, f x ∨ g x := by
-- proof
  obtain h | h := h
  · obtain ⟨x, hx, hfx⟩ := h
    exact ⟨x, hx, Or.inl hfx⟩
  · obtain ⟨x, hx, hgx⟩ := h
    exact ⟨x, hx, Or.inr hgx⟩


-- created on 2023-07-01
