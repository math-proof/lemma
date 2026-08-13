import Lemma.Bool.SEq.is.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Ge
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
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
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  rw [Dot.eq.SumMul.resize]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨i, by grind⟩)]
  erw [Dot.eq.GetSumMul.resize]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨0, by grind⟩)]
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  repeat rw [@Tensor.GetMul.eq.MulGetS.fin]
  apply SEqMulS.of.SEq.SEq
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [1, k', k ⊔ n']) (i := ⟨0, by grind⟩) (by grind) (by grind)]
  <;> conv_lhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [n, k', k ⊔ n']) (i := ⟨i, by grind⟩) (by grind) (by grind)];
  <;> apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
  ·
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    conv_rhs => erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqUnsqueezeS.of.SEq
    erw [EqGetUnsqueeze_0.fin]
    apply GetResize.as.ResizeGet.of.GtGet_0.GtVal_0 (by grind) (by grind)
  ·
    rw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    erw [Tensor.EqGetUnsqueeze_0.fin]
    erw [Tensor.EqGetUnsqueeze_0.nat.fin]


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) = X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.eq.DotGet.of.Lt h_n
  else
    apply GetDot.eq.DotGet.of.Ge (by omega)


-- created on 2026-01-05
-- updated on 2026-08-13
