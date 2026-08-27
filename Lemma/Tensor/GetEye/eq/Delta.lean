import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.special
open Tensor


@[main, fin]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
-- given
  (i j : Fin n) :
-- imply
  (Tensor.eye (α := α) n)[i, j] = KroneckerDelta i j := by
-- proof
  simp [Tensor.eye]
  have hrow := EqGetStack.fin (fun i : Fin n => [j < n] (↑(KroneckerDelta i j) : Tensor α [])) i
  have hcol := EqGetStack.fin (fun j : Fin n => (↑(KroneckerDelta i j) : Tensor α [])) j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]
  rfl


-- created on 2026-08-23
