import Initialize.Tactic.Attr.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Def.LinearAlgebra.Matrix.Permutation
import Lemma.Matrix.DotTShiftMatrix.eq.Eye
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  (x ᵥ* shiftMatrix (α := α) i j) ᵥ* shiftMatrix (α := α) j i = x := by
-- proof
  rw [vecMul_vecMul, DotTShiftMatrix.eq.Eye j i, vecMul_one]


-- created on 2020-11-14
