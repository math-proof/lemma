import Lemma.Tensor.Eq_Stack
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.AddStackS.eq.Stack_Add
open Tensor


@[main]
private lemma main
  [Add α]
-- given
  (A B : Tensor α (m :: s))
  (i : Fin m) :
-- imply
  (A + B)[i] = A[i] + B[i] := by
-- proof
  conv in (A + B)[i] =>
    rw [Eq_Stack A]
    rw [Eq_Stack B]
  rw [AddStackS.eq.Stack_Add]
  have := EqGetStack.fn fun i : Fin m => A[i] + B[i]
  simp_all


@[main]
private lemma fin
  [Add α]
-- given
  (A B : Tensor α (m :: s))
  (i : Fin m) :
-- imply
  (A + B).get i = A.get i + B.get i := by
-- proof
  apply main


-- created on 2025-07-20
