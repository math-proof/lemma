import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.GetMulCastS.eq.MulGetS
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Fin Tensor
set_option maxHeartbeats 10000000


/--
tensor version of Matrix.mul_apply
-/
@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = ∑ k : Fin l, A[i, k] * B[k, j] := by
-- proof
  simp [MatMul.dot]
  simp [Tensor.batch_dot]
  simp [GetElem.getElem]
  erw [GetSum_2.eq.SumGet__0.fin]
  erw [Sum_0.eq.Sum_Get.fin]
  apply Sum.of.All_Eq
  intro k
  apply GetMulCastS.eq.MulGetS


-- created on 2025-06-22
-- updated on 2026-07-09
