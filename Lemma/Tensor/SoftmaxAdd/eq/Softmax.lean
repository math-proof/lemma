import Lemma.Tensor.Add.eq.Add_KeepdimTensorReplicateProdEraseIdx
import Lemma.Tensor.SoftmaxAdd_Keepdim.eq.Softmax
open Tensor


@[main]
private lemma main
  [ExpRing α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  (X + δ).softmax d = X.softmax d := by
-- proof
  rw [Add.eq.Add_KeepdimTensorReplicateProdEraseIdx X δ d]
  apply SoftmaxAdd_Keepdim.eq.Softmax


-- created on 2025-11-30
-- updated on 2025-12-04
