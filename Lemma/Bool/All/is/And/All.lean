import sympy.Basic


@[main]
private lemma split
  {A : Set α}
  {p c : α → Prop} :
-- imply
  (∀ x ∈ A, p x) ↔ (∀ x ∈ A, c x → p x) ∧ ∀ x ∈ A, ¬c x → p x := by
-- proof
  constructor
  ·
    intro h
    exact ⟨fun x hx _ => h x hx, fun x hx _ => h x hx⟩
  ·
    rintro ⟨h₁, h₂⟩ x hx
    by_cases hc : c x
    ·
      exact h₁ x hx hc
    ·
      exact h₂ x hx hc


-- created on 2023-10-22
