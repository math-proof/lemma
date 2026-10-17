import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {A B : Matrix (Fin n) (Fin m) ℝ} :
-- imply
  A.transpose + B.transpose = (A + B).transpose := by
-- proof
  ext i j
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
