import sympy.Basic


@[main]
private lemma main
  {f : α → β}
  {g : α' → β'}
-- given
  (h₀ : α = α')
  (h₁ : β = β')
  (h₂ : ∀ (a : α), f a = cast h₁.symm (g (cast h₀ a))) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-07-16
