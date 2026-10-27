import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {v x : Fin n → ℝ} :
-- imply
  ∀ i, (Matrix.diagonal v).mulVec x i = v i * x i := by
-- proof
  intro i
  exact Matrix.mulVec_diagonal v x i


-- created on 2023-04-07
-- updated on 2026-10-26
