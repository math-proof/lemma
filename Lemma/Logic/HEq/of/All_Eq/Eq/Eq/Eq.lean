import Lemma.Basic


@[main]
private lemma main
  {f : α → β → γ → δ}
  {g : α' → β' → γ' → δ}
-- given
  (h₀ : α = α')
  (h₁ : β = β')
  (h₂ : γ = γ')
  (h₃ : ∀ (a : α) (b : β) (c : γ), f a b c = g (cast h₀ a) (cast h₁ b) (cast h₂ c)) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-07-16
