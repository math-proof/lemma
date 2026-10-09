import sympy.Basic


@[path]
private lemma main
  [DecidableEq α] [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {f : α → β}
  {g : β → α}
-- given
  (h₀ : ∀ a ∈ A, f a ∈ B)
  (h₁ : ∀ b ∈ B, g b ∈ A)
  (h₂ : ∀ a ∈ A, a = g (f a))
  (h₃ : ∀ b ∈ B, b = f (g b)) :
-- imply
  A.card = B.card :=
-- proof
  Finset.card_bij' (fun a _ => f a) (fun b _ => g b) h₀ h₁ (fun a ha => (h₂ a ha).symm) (fun b hb => (h₃ b hb).symm)


-- created on 2020-07-31
