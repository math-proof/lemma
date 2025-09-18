import Lemma.Basic


@[main]
private lemma main
  {X B : Set α}
-- given
  (h₁ : X ⊆ B)
  (A : Set α):
-- imply
  X ⊆ A ∪ B := by
-- proof
  intro x hx
  apply Or.inr
  exact h₁ hx


-- created on 2025-07-20
