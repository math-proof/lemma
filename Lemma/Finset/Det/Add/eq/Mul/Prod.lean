import Mathlib.LinearAlgebra.Matrix.SchurComplement
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a : Fin n → ℂ}
-- given
  (h : ∀ i, a i ≠ 0) :
-- imply
  (Matrix.of (fun _ _ => (1 : ℂ)) + Matrix.diagonal a).det = (1 + ∑ i, 1 / a i) * ∏ i, a i := by
-- proof
  have key : Matrix.of (fun _ _ => (1 : ℂ)) + Matrix.diagonal a = Matrix.diagonal a *
      (1 + Matrix.replicateCol Unit (fun i => (a i)⁻¹) * Matrix.replicateRow Unit (fun _ => (1 : ℂ))) := by
    ext i j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_apply,
      Fintype.sum_unique, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.of_apply, mul_one,
      mul_inv_cancel₀ (h i)]
    ring
  rw [key, Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow, Matrix.det_diagonal]
  simp only [dotProduct, one_mul, one_div]
  ring


-- created on 2020-10-04
