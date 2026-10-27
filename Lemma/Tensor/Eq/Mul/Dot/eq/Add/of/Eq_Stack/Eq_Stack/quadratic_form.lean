import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {x : Fin n → ℝ} :
-- imply
  dotProduct x (Matrix.mulVec A x) = ∑ i, ∑ j, x i * A i j * x j := by
-- proof
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]


-- created on 2026-10-11
-- updated on 2026-10-26
