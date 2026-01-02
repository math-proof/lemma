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
  rw [MulStack.eq.Stack_Mul]
  have := EqGetStack.fn fun i : Fin n => X[i] * a
  simp_all


-- created on 2025-12-06
