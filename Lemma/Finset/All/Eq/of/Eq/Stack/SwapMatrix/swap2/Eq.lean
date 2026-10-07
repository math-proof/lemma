import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {w : Fin (n + 1) → Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
  {i : Fin (n + 1)}
-- given
  (h : ∀ i j, w i j = swapMatrix i j) :
-- imply
  ∀ j ∈ Finset.univ \ {0, i}, w 0 i * w 0 j * w 0 i = w i j := by
-- proof
  have mul : ∀ (i j : Fin (n + 1)) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), swapMatrix i j * M = Matrix.of fun a b => M (Equiv.swap i j a) b := by
    intro i j M
    ext a b
    simp [swapMatrix, Matrix.mul_apply]
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hj
  obtain ⟨hjt, hji⟩ := hj
  rw [h 0 i, h 0 j, h i j, Matrix.mul_assoc, mul, mul]
  have key : ∀ a, Equiv.swap 0 j (Equiv.swap 0 i a) = Equiv.swap 0 i (Equiv.swap i j a) := by
    intro a
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  ext a b
  simp only [Matrix.of_apply, swapMatrix, key, Equiv.swap_apply_self]


-- created on 2020-08-23
