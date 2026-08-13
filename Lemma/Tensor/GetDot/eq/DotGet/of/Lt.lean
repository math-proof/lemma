import Lemma.Bool.Cast.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.Dot.eq.SumMulResize_0.of.Lt
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSumS.of.SEq
open Bool List Nat Tensor
set_option maxHeartbeats 500000


@[main, fin]
private lemma main
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
  rw [Dot.eq.SelectSumMul.resize]
  rw [EqMax.of.Lt h]
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
    erw [EqGetUnsqueeze_0.nat.fin (z := ⟨i % 1, by grind⟩) ((Y.resize 0 n').unsqueeze 0)]
    erw [EqGetUnsqueeze_0.fin]
    apply SEqResize_0.of.Eq_Get_0.GtLength_0 (by simp) (by grind)


-- created on 2026-01-10
-- updated on 2026-08-13
