import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A : Finset α}
  {B : Finset β}
  {f : α → β}
  {g : β → α}
-- given
  (h₀ : ∀ a ∈ A, f a ∈ B ∧ g (f a) = a)
  (h₁ : ∀ b ∈ B, g b ∈ A ∧ f (g b) = b) :
-- imply
  A.card = B.card := by
-- proof
  exact Finset.card_nbij' f g (fun a ha => (h₀ a ha).1) (fun b hb => (h₁ b hb).1) (fun a ha => (h₀ a ha).2) (fun b hb => (h₁ b hb).2)


-- created on 2020-08-01
