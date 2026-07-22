import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq_Stack
import Lemma.Tensor.MulStack.eq.Stack_Mul
open Tensor


@[main, fin]
private lemma main
  [Mul α]
-- given
  (X : Tensor α (n :: s))
  (a : α)
  (i : Fin n) :
-- imply
  (X * a)[i] = X[i] * a := by
-- proof
  conv in (X * a)[i] =>
    rw [Eq_Stack X]
  erw [MulStack.eq.Stack_Mul.scalar]
  have := EqGetStack.fn.fin fun i : Fin n => X[i] * a
  simp [GetElem.getElem] at this ⊢
  rw [this]


-- created on 2025-12-06
