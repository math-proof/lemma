import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.Dot.eq.GetSumMul.of.Lt
import Lemma.Tensor.Dot.eq.SelectSumMul.of.Lt
import Lemma.Tensor.Dot.eq.SumMul.of.Lt
import Lemma.Tensor.Dot.eq.SumMulResize_0.of.Lt
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  rw [Dot.eq.SumMul.of.Lt h]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨i, by grind⟩)]
  erw [Dot.eq.GetSumMul.of.Lt h]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨0, by grind⟩)]
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  repeat rw [@Tensor.GetMul.eq.MulGetS.fin]
  apply SEq.of.Eq
  congr 1
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [n, k', n']) (i := ⟨i, by grind⟩) (by grind) (by grind)]
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [1, k', n']) (i := ⟨0, by grind⟩) (by grind) (by grind)]
  <;> apply EqCastS.of.SEq.Eq (by simp)
  ·
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEq.of.Eq ∘ EqCastS.of.SEq.Eq (by simp)
    simp
    apply SEqRepeatS.of.SEq
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    conv_rhs => erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    apply SEq.of.Eq ∘ EqCastS.of.SEq.Eq (by simp)
    apply SEqUnsqueezeS.of.SEq
    erw [EqGetUnsqueeze_0.fin]
    erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by grind) (by simp; grind)]
    simp
    rfl
  ·
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    apply SEq.of.Eq ∘ EqCastS.of.SEq.Eq (by simp)
    apply SEq.of.Eq
    simp
    grind


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  rw [Dot.eq.SelectSumMul.of.Lt h]
  erw [GetSelect_1.eq.Cast_Get.of.Lt.GtGet_0.GtLength_0 (by grind) (by grind) (by grind)]
  erw [Dot.eq.SumMulResize_0.of.Lt h]
  apply EqCast.of.SEq.Eq (by simp)
  erw [GetSum_2.eq.SumGet__0.fin]
  apply SEqSumS.of.SEq
  erw [@Tensor.GetMul.eq.MulGetS.fin]
  erw [@Tensor.GetMul.eq.MulGetS.fin]
  apply SEq.of.Eq
  congr 1
  ·
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    simp
    erw [EqGetUnsqueeze_0.fin]
    erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by grind) (by simp; grind)]
    apply EqCast.of.SEq.Eq (by simp)
    simp
    rfl
  ·
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [n, 1, n']) (i := ⟨i, by grind⟩) (by grind) (by grind)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [1, n']) (i := ⟨0, by grind⟩) (by grind) (by grind)]
    apply EqCast.of.SEq.Eq (by simp)
    simp
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [1, n']) (i := ⟨0, by grind⟩) (by grind) (by grind)]
    apply SEq.of.Eq ∘ EqCast.of.SEq.Eq (by simp)
    simp
    erw [EqGetUnsqueeze_0.nat.fin (z := ⟨i % 1, by grind⟩) (Y.unsqueeze 0)]
    erw [EqGetUnsqueeze_0.fin]


-- created on 2026-01-10
-- updated on 2026-07-14
