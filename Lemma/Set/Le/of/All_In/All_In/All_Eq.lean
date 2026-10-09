import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Finset ℤ}
  {f g : ℤ → ℤ}
-- given
  (h₀ : ∀ a ∈ A, f a ∈ B)
  (_ : ∀ b ∈ B, g b ∈ A)
  (h₂ : ∀ a ∈ A, a = g (f a)) :
-- imply
  A.card ≤ B.card := by
-- proof
  apply Finset.card_le_card_of_injOn f h₀
  intro a h_a a' h_a' h
  rw [h₂ a (Finset.mem_coe.mp h_a), h₂ a' (Finset.mem_coe.mp h_a'), h]


-- created on 2021-01-08
