import Lemma.Basic


@[main]
private lemma main
  {f : α → β → γ}
  {g : α' → β' → γ}
-- given
  (h₀ : α = α')
  (h₁ : β = β')
  (h : ∀ (a : α) (b : β), f a b = g (cast h₀ a) (cast h₁ b)) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-07-16
