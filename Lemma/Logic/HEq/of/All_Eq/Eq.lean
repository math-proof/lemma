import Lemma.Basic


@[main]
private lemma main
  {f : α → β}
  {g : α' → β}
  -- given
  (h₀ : α = α')
  (h₁ : ∀ (a : α), f a = g (cast h₀ a)) :
-- imply
  HEq f g := by
-- proof
  aesop


@[main]
private lemma fin
  {f : Fin n → β}
  {g : Fin m → β}
  -- given
  (h₀ : n = m)
  (h₁ : ∀ (i : Fin n), f i = g ⟨i, by simp_all [← h₀]⟩) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-07-15
