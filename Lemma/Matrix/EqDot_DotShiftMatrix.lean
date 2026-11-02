import Initialize.Tactic.Attr.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Def.LinearAlgebra.Matrix.Permutation
import Lemma.Matrix.EqTShiftMatrix
import Lemma.Matrix.DotTShiftMatrix.eq.Eye
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  (shiftMatrix (α := α) i j)ᵀ *ᵥ ((shiftMatrix (α := α) i j) *ᵥ x) = x := by
-- proof
  rw [mulVec_mulVec, EqTShiftMatrix (α := α) i j, DotTShiftMatrix.eq.Eye i j,
    one_mulVec]


-- created on 2026-11-01
