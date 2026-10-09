import sympy.Basic


@[path]
private lemma split
  {A : Set α}
  {f c : α → Prop}
-- given
  (h : ∃ x ∈ A, f x) :
-- imply
  (∃ x ∈ A ∩ {x | c x}, f x) ∨ ∃ x ∈ A \ {x | c x}, f x := by
-- proof
  obtain ⟨x, hx, hf⟩ := h
  by_cases hc : c x
  ·
    exact Or.inl ⟨x, ⟨hx, hc⟩, hf⟩
  ·
    exact Or.inr ⟨x, ⟨hx, hc⟩, hf⟩


-- created on 2023-10-22
