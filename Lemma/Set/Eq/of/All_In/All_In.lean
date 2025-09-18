import Lemma.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h₀ : ∀ x ∈ A, x ∈ B)
  (h₁ : ∀ x ∈ B, x ∈ A) :
-- imply
  A = B := by
-- proof
  aesop


@[main]
private lemma fin
  {A B : Finset α}
-- given
  (h₀ : ∀ x ∈ A, x ∈ B)
  (h₁ : ∀ x ∈ B, x ∈ A) :
-- imply
  A = B := by
-- proof
  aesop


-- created on 2025-07-20
