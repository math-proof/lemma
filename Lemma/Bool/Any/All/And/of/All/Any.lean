import sympy.Basic


@[main]
private lemma main
  {A : β → Set α}
  {B : Set β}
  {f : β → α → Prop}
  {g : β → Prop}
-- given
  (h₀ : ∀ y, ∀ x ∈ A y, f y x)
  (h₁ : ∃ y ∈ B, g y) :
-- imply
  ∃ y ∈ B, ∀ x ∈ A y, f y x ∧ g y := by
-- proof
  obtain ⟨y, hy, hg⟩ := h₁
  exact ⟨y, hy, fun x hx => ⟨h₀ y x hx, hg⟩⟩


-- created on 2026-09-27
