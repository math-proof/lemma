import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {B : Set β}
  {p : α → β → Prop}
-- given
  (h : ∀ x ∈ A, ∃ y ∈ B, p x y) :
-- imply
  ∀ x ∈ A, ∃ y ∈ B, p x y ∧ x ∈ A := by
-- proof
  intro x hx
  obtain ⟨y, hy, hp⟩ := h x hx
  exact ⟨y, hy, hp, hx⟩


-- created on 2021-09-15
