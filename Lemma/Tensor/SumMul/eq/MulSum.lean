import Lemma.Tensor.Mul.eq.Mul_KeepdimTensorReplicateProdEraseIdx
import Lemma.Tensor.Mul.eq.Mul_TensorReplicateProd
import Lemma.Tensor.SumMul_Keepdim.eq.MulSum
open Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s)
  (d : ℕ)
  (a : α) :
-- imply
  (X * a).sum d = X.sum d * a := by
-- proof
  rw [Mul.eq.Mul_KeepdimTensorReplicateProdEraseIdx]
  rw [SumMul_Keepdim.eq.MulSum]
  rw [Mul.eq.Mul_TensorReplicateProd]


-- created on 2025-12-01
-- updated on 2025-12-04
