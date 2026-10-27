import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m n : ℕ} :
-- imply
  ∀ (i : Fin m) (j : Fin n), (Matrix.of fun (_ : Fin m) (_ : Fin n) => (1 : ℝ)) i j = 1 := by
-- proof
  intro i j
  rfl


-- created on 2021-10-04
-- updated on 2026-10-26
