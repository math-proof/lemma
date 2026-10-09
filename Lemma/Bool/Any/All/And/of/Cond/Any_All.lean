import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {c : Prop}
  {g : α → β → Prop}
-- given
  (h₀ : c)
  (h₁ : ∃ y ∈ B, ∀ x ∈ A, g x y) :
-- imply
  ∃ y ∈ B, ∀ x ∈ A, c ∧ g x y := by
-- proof
  obtain ⟨y, hy, h⟩ := h₁
  exact ⟨y, hy, fun x hx => ⟨h₀, h x hx⟩⟩


-- created on 2019-03-14
