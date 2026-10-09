import sympy.Basic


@[path]
private lemma given
  {A : Set α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ x ∈ A, p x)
  (h₁ : ∀ x ∈ A, q x) :
-- imply
  ∀ x ∈ A, p x ∧ q x :=
-- proof
  fun x hx => ⟨h₀ x hx, h₁ x hx⟩


-- created on 2021-08-25
