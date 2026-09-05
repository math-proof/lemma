import Mathlib.Data.Matrix.Diagonal
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.GetEye.eq.Delta
import sympy.matrices.dense
import sympy.matrices.expressions.special
open Nat Tensor


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α] :
-- imply
  (Tensor.eye (α := α) n).toMatrix = 1 := by
-- proof
  ext i j
  apply Eq.trans (GetEye.eq.Delta.fin (α := α) i j)
  simp only [Matrix.one_apply]
  rw [Delta.eq.Ite]
  if hij : i = j then
    simp [hij]
    apply cast_one
  else
    simp [hij]
    apply cast_zero


-- created on 2026-09-05
