import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Fin.Sum.of.All_Eq
import Lemma.List.EqSwap_0'1
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.EqGetS.of.Eq
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Bool Fin List Nat Tensor
set_option maxHeartbeats 20000000


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
  erw [Sum_0.eq.Sum_Get.fin]
  apply Sum.of.All_Eq
  intro k
  erw [GetMul.eq.MulGetS.fin _ _ i]
  erw [GetMul.eq.MulGetS.fin _ _ j]
  erw [GetMul.eq.MulGetS.fin _ _ k]
  congr 1
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) (by simp) (i := ⟨i, by simp⟩)]
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp) (i := ⟨j, by simp⟩)]
  <;> simp
  ·
    apply EqGetS.of.Eq.fin
    erw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (i := i) (by simp) (by simp)]
    simp
    erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    simp [EqMod_1'0]
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) (by simp) (by grind)]
    simp
    erw [EqGetUnsqueeze.fin]
  ·
    erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    simp
    erw [EqGetUnsqueeze.nat.fin]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp [EqSwap_0'1]) (by simp [EqSwap_0'1]) (i := ⟨j, by simp [EqSwap_0'1]⟩)]
    simp
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp [EqSwap_0'1]) (by simp [EqSwap_0'1]) (i := ⟨k, by simp [EqSwap_0'1]⟩)]
    simp
    apply EqCast.of.SEq
    apply SEq.of.Eq
    erw [GetTranspose.eq.Get.fin B]
    rfl


-- created on 2025-06-22
-- updated on 2026-07-08
