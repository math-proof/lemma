import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {A B : Matrix (Fin n) (Fin m) ℝ} :
-- imply
  Matrix.of (fun i j => A.transpose i j / B.transpose i j) = (Matrix.of fun i j => A i j / B i j).transpose := by
-- proof
  ext i j
  simp [Matrix.transpose_apply]


-- created on 2026-10-11
-- updated on 2026-10-17
