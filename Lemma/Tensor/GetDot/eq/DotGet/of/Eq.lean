import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq
import Lemma.Vector.GetMul.eq.MulGetS
open Bool Nat Tensor Vector
set_option maxHeartbeats 10000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [k, k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i] = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  erw [Dot.eq.GetSumMul]
  rw [Dot.eq.SumMul]
  rw [GetSum_2.eq.SumGet__1.fin]
  erw [GetSum_2.eq.SumGet__1.fin]
  simp
  apply EqSumS.of.Eq
  simp [@Tensor.GetMul.eq.MulGetS.fin]
  congr 1
  <;>
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
  <;>
  simp
  ·
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨0, by grind⟩) (by simp) (by simp)]
    apply EqCastS.of.SEq.Eq (by simp)
    simp
    erw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (i := i) (n := k') (d := ⟨1, by grind⟩) (by simp) (by simp)]
    erw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (i := 0) (n := k') (d := ⟨1, by grind⟩) (by simp) (by simp)]
    simp
    apply SEqRepeatS.of.SEq
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (i := i) (by simp) (by simp) (by simp)]
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (i := 0) (by simp) (by simp) (by simp)]
    simp
    apply SEqUnsqueezeS.of.SEq
    erw [EqGetUnsqueeze_0.fin]
  ·
    erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (i := i) (n := n) (by simp) (by simp)]
    erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (i := 0) (n := 1) (by simp) (by simp)]
    simp [EqMod_1'0]


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [k])
  (i : Fin n) :
-- imply
  (X @ Y)[i] = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  rw [Dot.eq.SelectSumMul]
  simp
  erw [Dot.eq.SumMul__0]
  erw [GetSelect_1.eq.Cast_Get.of.Lt_Get_0.Lt_Get_1.GtLength_1 (by simp) (by simp) (by grind)]
  apply EqCast.of.SEq.Eq (by simp)
  erw [GetSum_2.eq.SumGet__0.fin]
  apply SEqSumS.of.SEq
  erw [@Tensor.GetMul.eq.MulGetS.fin]
  erw [@Tensor.GetMul.eq.MulGetS.fin]
  apply SEq.of.Eq
  congr 1
  ·
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by grind) (i := ⟨0, by grind⟩)]
    apply EqCast.of.SEq.Eq (by simp)
    simp
    apply SEq.of.Eq
    apply EqGetUnsqueeze_0.fin
  ·
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp) (i := ⟨i, by grind⟩) (s' := [n, 1, k])]
    simp
    erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by grind) (i := ⟨0, by grind⟩)]
    apply EqCast.of.SEq.Eq (by simp)
    simp
    erw [EqGetUnsqueeze_0.nat.fin]
    erw [EqGetUnsqueeze_0.nat.fin]


-- created on 2026-07-10
-- updated on 2026-07-12
