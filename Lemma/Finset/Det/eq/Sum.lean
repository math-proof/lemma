import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  A.det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A i (σ i) := by
-- proof
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl


@[main]
private lemma expansion_by_minors
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
  {i : Fin (n + 1)} :
-- imply
  A.det = ∑ j, A i j * ((-1) ^ ((i : ℕ) + j) * (A.submatrix i.succAbove j.succAbove).det) := by
-- proof
  rw [Matrix.det_succ_row A i]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


-- created on 2026-09-27
