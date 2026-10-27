import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  (A * B).conjTranspose = B.conjTranspose * A.conjTranspose := by
-- proof
  simp


-- created on 2023-06-23
-- updated on 2026-10-26
