import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {A B : Matrix (Fin n) (Fin m) ℝ} :
-- imply
  A.transpose + B.transpose = (A + B).transpose := by
-- proof
  ext i j
  simp


-- created on 2018-08-10
-- updated on 2026-10-26
