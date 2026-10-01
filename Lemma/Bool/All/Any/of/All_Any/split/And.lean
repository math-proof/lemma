import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {B : Set β}
  {p q : α → β → Prop}
-- given
  (h : ∀ x ∈ A, ∃ y ∈ B, p x y ∧ q x y) :
-- imply
  ∀ x ∈ A, ∃ y ∈ B, p x y := by
-- proof
  intro x hx
  obtain ⟨y, hy, hp, _⟩ := h x hx
  exact ⟨y, hy, hp⟩


-- created on 2018-12-23
