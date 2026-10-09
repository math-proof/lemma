import sympy.Basic


@[path]
private lemma given
  {A : Set α}
  {B : Set β}
  {p : α → β → Prop}
-- given
  (h : ∀ x ∈ A, ∃ y ∈ B, p x y ∧ y ∈ B) :
-- imply
  ∀ x ∈ A, ∃ y ∈ B, p x y := by
-- proof
  intro x hx
  obtain ⟨y, hy, hp, _⟩ := h x hx
  exact ⟨y, hy, hp⟩


-- created on 2021-09-15
