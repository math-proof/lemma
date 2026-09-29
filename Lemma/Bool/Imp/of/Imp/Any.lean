import sympy.Basic


@[main]
private lemma given
  {p q : α → Prop}
-- given
  (h₀ : (∃ x, p x) → ∃ x, q x)
  (h₁ : ∀ x y, q x → q y) :
-- imply
  ∀ x, p x → q x := by
-- proof
  intro x hx
  obtain ⟨y, hy⟩ := h₀ ⟨x, hx⟩
  exact h₁ y x hy


-- created on 2026-09-27
