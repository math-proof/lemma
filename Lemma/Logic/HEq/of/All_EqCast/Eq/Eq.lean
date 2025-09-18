import Lemma.Basic


@[main]
private lemma main
  {f : α → β}
  {g : α' → β'}
-- given
  (h₀ : α = α')
  (h₁ : β = β')
  (h₂ : ∀ (a : α), cast h₁ (f a) = g (cast h₀ a)) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-07-16
