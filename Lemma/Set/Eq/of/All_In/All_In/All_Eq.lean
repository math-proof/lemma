import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → β}
  {g : β → α}
-- given
  (h₀ : ∀ a ∈ A, f a ∈ B)
  (h₁ : ∀ b ∈ B, g b ∈ A)
  (h₂ : ∀ a ∈ A, a = g (f a)) :
-- imply
  g '' B = A := by
-- proof
  ext a
  constructor
  ·
    rintro ⟨b, hb, rfl⟩
    exact h₁ b hb
  ·
    intro ha
    exact ⟨f a, h₀ a ha, (h₂ a ha).symm⟩


-- created on 2020-07-30
