import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.Defs


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i₀ j₀ i j : Fin n) :
-- imply
  (shiftMatrix (α := α) i₀ j₀) i j =
    (KroneckerDelta (i.shiftRow i₀ j₀) j : α) := by
-- proof
  simp [shiftMatrix, Matrix.of_apply]


-- created on 2026-11-01
