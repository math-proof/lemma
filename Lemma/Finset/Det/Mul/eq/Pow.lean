import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {a : ℂ} :
-- imply
  (a • (1 : Matrix (Fin n) (Fin n) ℂ)).det = a ^ n := by
-- proof
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]


-- created on 2026-09-27
