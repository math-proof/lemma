import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {p q : α → Prop} :
-- imply
  (∀ x ∈ A, p x ∧ q x) ↔ (∀ x ∈ A, p x) ∧ ∀ x ∈ A, q x := by
-- proof
  constructor
  ·
    intro h
    exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  ·
    rintro ⟨h₁, h₂⟩ x hx
    exact ⟨h₁ x hx, h₂ x hx⟩


-- created on 2026-09-27
