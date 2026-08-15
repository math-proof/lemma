import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.Div.eq.Div_KeepdimTensorReplicateProdEraseIdx
import Lemma.Tensor.Div.eq.Div_TensorReplicate
import Lemma.Tensor.SumDiv_Keepdim.eq.DivSum
open Tensor


@[main]
private lemma scalar
  [DivisionSemiring α]
-- given
  (X : Tensor α s)
  (d : ℕ)
  (a : α) :
-- imply
  (X / a).sum d = X.sum d / a := by
-- proof
  rw [Div.eq.Div_KeepdimTensorReplicateProdEraseIdx]
  rw [SumDiv_Keepdim.eq.DivSum]
  rw [Div.eq.Div_TensorReplicate]


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (X : Tensor α s)
  (n : Tensor α [])
  (d : ℕ) :
-- imply
  (X / n).sum d = X.sum d / n := by
-- proof
  rw [Div.eq.Div_GetData_0]
  apply scalar


-- created on 2025-09-21
-- updated on 2026-08-15
