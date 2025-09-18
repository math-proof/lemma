import Lemma.Basic


@[main]
private lemma main
  {X A B : Set α}
-- given
  (h₀ : X ⊆ A)
  (h₁ : X ⊆ B) :
-- imply
  X ⊆ A ∩ B := by
-- proof
  intro x hx
  exact ⟨h₀ hx, h₁ hx⟩


-- created on 2025-07-20
