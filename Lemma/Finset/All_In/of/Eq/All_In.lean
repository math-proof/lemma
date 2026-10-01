import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma swap2
  {n : ℕ}
  {S : Set (Fin (n + 1) → ℂ)}
  {w : Fin (n + 1) → Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
  {i j : Fin (n + 1)}
-- given
  (h₀ : ∀ i j, w i j = swapMatrix i j)
  (h₁ : ∀ j, ∀ x ∈ S, w 0 j *ᵥ x ∈ S) :
-- imply
  ∀ x ∈ S, w i j *ᵥ x ∈ S := by
-- proof
  have mulv : ∀ (a c : Fin (n + 1)) (y : Fin (n + 1) → ℂ), swapMatrix a c *ᵥ y = y ∘ Equiv.swap a c := by
    intro a c y
    funext r
    simp [swapMatrix, Matrix.mulVec, dotProduct]
  have h1 : ∀ k, ∀ x ∈ S, x ∘ Equiv.swap 0 k ∈ S := fun k x hx => by
    rw [← mulv, ← h₀]
    exact h₁ k x hx
  intro x hx
  rw [h₀, mulv]
  by_cases hji : j = i
  · rw [hji, Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
    exact hx
  by_cases hi0 : i = 0
  · rw [hi0]
    exact h1 j x hx
  by_cases hj0 : j = 0
  · rw [hj0, Equiv.swap_comm]
    exact h1 i x hx
  have key : x ∘ Equiv.swap i j = ((x ∘ Equiv.swap 0 i) ∘ Equiv.swap 0 j) ∘ Equiv.swap 0 i := by
    funext c
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [key]
  exact h1 i _ (h1 j _ (h1 i x hx))


-- created on 2020-08-25
