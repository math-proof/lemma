import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {w : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ}
  {i j : Fin n}
-- given
  (h : ∀ i j, w i j = swapMatrix i j) :
-- imply
  w i j * w i j = 1 := by
-- proof
  have mul : ∀ (i j : Fin n) (M : Matrix (Fin n) (Fin n) ℂ), swapMatrix i j * M = Matrix.of fun a b => M (Equiv.swap i j a) b := by
    intro i j M
    ext a b
    simp [swapMatrix, Matrix.mul_apply]
  rw [h i j, mul]
  ext a b
  simp only [Matrix.of_apply, swapMatrix, Equiv.swap_apply_self, Matrix.one_apply]
  by_cases hab : a = b <;> simp [hab, eq_comm]


-- created on 2020-08-24
