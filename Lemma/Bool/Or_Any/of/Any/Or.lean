import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : ∃ x ∈ A, g x ∨ f x) :
-- imply
  (∃ x ∈ A, g x) ∨ ∃ x ∈ A, f x := by
-- proof
  obtain ⟨x, hx, h | h⟩ := h
  ·
    exact Or.inl ⟨x, hx, h⟩
  ·
    exact Or.inr ⟨x, hx, h⟩


-- created on 2023-07-01
