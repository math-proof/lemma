import Def.LinearAlgebra.Matrix.Permutation
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {w : Fin (n + 1) → Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
-- given
  (h₀ : ∀ i j, w i j = swapMatrix i j)
  (t i : Fin (n + 1)) :
-- imply
  ∀ j ∈ Finset.univ \ {i, t}, w t i * w t j * w t i = w i j := by
-- proof
  have mul : ∀ (p q : Fin (n + 1)) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      swapMatrix p q * M = Matrix.of fun a b => M (Equiv.swap p q a) b := by
    intro p q M
    ext a b
    simp [swapMatrix, Matrix.mul_apply]
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hj
  obtain ⟨hji, hjt⟩ := hj
  rw [h₀ t i, h₀ t j, h₀ i j, Matrix.mul_assoc, mul, mul]
  have key : ∀ a, Equiv.swap t j (Equiv.swap t i a) = Equiv.swap t i (Equiv.swap i j a) := by
    intro a
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  ext a b
  simp only [Matrix.of_apply, swapMatrix, key, Equiv.swap_apply_self]


-- created on 2020-08-23
-- updated on 2026-10-26
