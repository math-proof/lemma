import Lemma.Tensor.Mul.eq.Mul_GetData_0
import Lemma.Tensor.Mul.eq.Mul_KeepdimTensorReplicateProdEraseIdx
import Lemma.Tensor.Mul.eq.Mul_TensorReplicate
import Lemma.Tensor.SumMul_Keepdim.eq.MulSum
open Tensor


@[main]
private lemma scalar
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
  rw [Mul.eq.Mul_TensorReplicate]


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s)
  (n : Tensor α [])
  (d : ℕ) :
-- imply
  (X * n).sum d = X.sum d * n := by
-- proof
  rw [Mul.eq.Mul_GetData_0]
  rw [scalar]
  rw [← Mul.eq.Mul_GetData_0]


-- created on 2025-12-01
-- updated on 2026-08-15
