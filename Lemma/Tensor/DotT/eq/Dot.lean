import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.EqMax.of.Ge
import Lemma.Nat.EqMax.of.Lt
import Lemma.Nat.Mul
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul.of.Ge
import Lemma.Tensor.Dot.eq.SelectSumMul.of.Lt
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.UnsqueezeUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.SEqResizeS.of.SEq.Val.Eq
import Lemma.Tensor.SEqSelectUnsqueeze.of.GeLength
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Tensor.SelectMul.eq.MulSelectS
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt
import Lemma.Tensor.SelectSum.as.SumSelect.of.Gt
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Lt.GeLength
open Bool Nat Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (X : Tensor α [n, m])
  (Y : Tensor α [n]) :
-- imply
  Xᵀ @ Y = Y @ X := by
-- proof
  rw [Dot.eq.GetSumMul]
  conv_lhs => erw [Dot.eq.SelectSumMul]
  conv_lhs => erw [SelectSum.eq.Cast_SumSelect.of.Gt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
  simp
  erw [GetSum_2.eq.SumGet__1.fin]
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  erw [SelectMul.eq.MulSelectS]
  erw [GetMul.eq.MulGetS.fin]
  apply SEq.of.Eq
  rw [Mul.comm]
  congr 1
  ·
    erw [SelectCast.eq.Cast_Select.of.Eq (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨0, by grind⟩) (by grind) (by grind)]
    apply EqCastS.of.SEq.Eq (by simp)
    erw [UnsqueezeUnsqueeze_0]
    erw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
    rw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEq.of.Eq
    apply EqCastS.of.SEq.Eq (by simp)
    simp
    apply SEq.of.Eq
    congr 1
    erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by grind⟩)]
    simp
    erw [EqGetUnsqueeze_0.fin]
    erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
    simp
  ·
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
    simp
    erw [EqGetUnsqueeze_0.fin]


@[main]
private lemma resize
  [CommMagma α] [AddCommMonoid α]
  (X : Tensor α [n, m])
  (Y : Tensor α [n']) :
  Xᵀ @ Y = Y @ X := by
  by_cases h_eq : n' = n
  · subst h_eq; apply main
  · rcases Nat.lt_or_gt_of_ne h_eq with h | h
    ·
      rw [Dot.eq.GetSumMul.of.Lt h]
      conv_lhs => erw [Dot.eq.SelectSumMul.of.Ge (Nat.le_of_lt h)]
      conv_lhs => erw [SelectSum.eq.Cast_SumSelect.of.Gt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
      simp
      erw [GetSum_2.eq.SumGet__1.fin]
      apply Eq.of.SEq
      apply SEqSumS.of.SEq
      erw [SelectMul.eq.MulSelectS]
      erw [GetMul.eq.MulGetS.fin]
      apply SEq.of.Eq
      rw [Mul.comm]
      congr 1
      ·
        erw [SelectCast.eq.Cast_Select.of.Eq (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
        erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨0, by grind⟩) (by grind) (by grind)]
        apply EqCastS.of.SEq.Eq (by simp)
        erw [UnsqueezeUnsqueeze_0]
        erw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
        rw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
        apply SEq.of.Eq
        apply EqCastS.of.SEq.Eq (by simp)
        simp
        apply SEq.of.Eq
        congr 1
        erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by grind⟩)]
        simp
        erw [EqGetUnsqueeze_0.fin]
        erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
        simp
      ·
        erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
        erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
        simp
        erw [EqGetUnsqueeze_0.fin]
    ·
      rw [Dot.eq.GetSumMul.of.Ge (Nat.le_of_lt h)]
      conv_lhs => erw [Dot.eq.SelectSumMul.of.Lt h]
      conv_lhs => erw [SelectSum.eq.Cast_SumSelect.of.Gt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
      simp
      erw [GetSum_2.eq.SumGet__1.fin]
      apply Eq.of.SEq
      apply SEqSumS.of.SEq
      erw [SelectMul.eq.MulSelectS]
      erw [GetMul.eq.MulGetS.fin]
      apply SEq.of.Eq
      rw [Mul.comm]
      congr 1
      ·
        erw [SelectCast.eq.Cast_Select.of.Eq (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
        erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨0, by grind⟩) (by grind) (by grind)]
        apply EqCastS.of.SEq.Eq (by simp)
        erw [UnsqueezeUnsqueeze_0]
        erw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
        rw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
        apply SEq.of.Eq
        apply EqCastS.of.SEq.Eq (by simp)
        simp
        apply SEq.of.Eq
        congr 1
        erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by grind⟩)]
        simp
        erw [EqGetUnsqueeze_0.fin]
        erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
        simp
      ·
        erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
        erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
        simp
        erw [EqGetUnsqueeze_0.fin]


-- created on 2026-07-30
