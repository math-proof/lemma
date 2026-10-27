import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  (∑ i, x i * y i) = dotProduct x y := by
-- proof
  simp [dotProduct]


-- created on 2023-09-18
-- updated on 2026-10-26
