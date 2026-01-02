import Lemma.Tensor.Eq_Stack
import Lemma.Tensor.MulStackS.eq.Stack_Mul
import Lemma.Tensor.EqGetStack
open Tensor


@[main, fin]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  (A * B)[i] = A[i] * B[i] := by
-- proof
  conv in (A * B)[i] =>
    rw [Eq_Stack A]
    rw [Eq_Stack B]
  rw [MulStackS.eq.Stack_Mul]
  have := EqGetStack.fn fun i : Fin n => A[i] * B[i]
  simp_all


-- created on 2025-07-13
