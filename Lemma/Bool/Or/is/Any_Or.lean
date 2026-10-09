import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {f g : α → Prop} :
-- imply
  (∃ x ∈ A, g x) ∨ (∃ x ∈ A, f x) ↔ ∃ x ∈ A, g x ∨ f x := by
-- proof
  constructor
  ·
    rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    ·
      exact ⟨x, hx, Or.inl h⟩
    ·
      exact ⟨x, hx, Or.inr h⟩
  ·
    rintro ⟨x, hx, h | h⟩
    ·
      exact Or.inl ⟨x, hx, h⟩
    ·
      exact Or.inr ⟨x, hx, h⟩


-- created on 2020-02-20
