import sympy.Basic


@[main]
private lemma given
  {A B : Set α}
  {f : α → Prop}
-- given
  (h : ∃ x ∈ A ∪ B, f x) :
-- imply
  (∃ x ∈ A, f x) ∨ ∃ x ∈ B, f x := by
-- proof
  obtain ⟨x, hx | hx, h⟩ := h
  ·
    exact Or.inl ⟨x, hx, h⟩
  ·
    exact Or.inr ⟨x, hx, h⟩


-- created on 2020-02-17
