import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma swap2.eq_general
  {n : ℕ}
  {w : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ}
  {i t : Fin n}
-- given
  (h : ∀ i j, w i j = swapMatrix i j) :
-- imply
  ∀ j ∈ Finset.univ \ {i, t}, w t i * w t j * w t i = w i j := by
-- proof
  have mul : ∀ (i j : Fin n) (M : Matrix (Fin n) (Fin n) ℂ), swapMatrix i j * M = Matrix.of fun a b => M (Equiv.swap i j a) b := by
    intro i j M
    ext a b
    simp [swapMatrix, Matrix.mul_apply]
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hj
  obtain ⟨hji, hjt⟩ := hj
  rw [h t i, h t j, h i j, Matrix.mul_assoc, mul, mul]
  have key : ∀ a, Equiv.swap t j (Equiv.swap t i a) = Equiv.swap t i (Equiv.swap i j a) := by
    intro a
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  ext a b
  simp only [Matrix.of_apply, swapMatrix, key, Equiv.swap_apply_self]


-- created on 2026-09-27
