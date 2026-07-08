import Lemma.List.EqSwap_0'1
import Lemma.Tensor.GetCast_Get.eq.Get_Cast_Repeat
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.RepeatCast.eq.Cast_Repeat
import Lemma.Tensor.UnsqueezeCast.eq.Cast_Unsqueeze
open List Tensor Nat
set_option maxHeartbeats 10000000


/--
tensor version of Matrix.mul_apply
-/
@[main]
private lemma main
  [Mul α]
  [AddCommMonoid α]
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
  erw [GetMul.eq.MulGetS.fin _ _ i]
  erw [GetMul.eq.MulGetS.fin _ _ j]
  have := UnsqueezeCast.eq.Cast_Unsqueeze B
  simp at this
  erw [this]
  have := RepeatCast.eq.Cast_Repeat B m
  simp at this
  erw [this]
  have := GetCast_Get.eq.Get_Cast_Repeat B i
  simp at this
  erw [this]
  sorry


-- created on 2025-06-22
-- updated on 2026-07-08
