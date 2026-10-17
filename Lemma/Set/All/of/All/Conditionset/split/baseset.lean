import sympy.Basic


@[path]
private lemma main
  {B s : Set α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ x ∈ {y | y ∈ B ∧ p y}, q x)
  (h₁ : s = {y | y ∈ B ∧ p y}) :
-- imply
  ∀ x ∈ s, q x := by
-- proof
  intro x hx
  rw [h₁] at hx
  exact h₀ x hx


-- created on 2026-10-11
-- updated on 2026-10-17
