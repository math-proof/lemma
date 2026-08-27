import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Nat.Max
import Lemma.Nat.Mul
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.ResizeT_1.eq.TResize_0
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.Val.Eq
import Lemma.Tensor.SEqResizeS.of.SEq.Val.Eq
import Lemma.Tensor.SEqSelectUnsqueeze.of.GeLength
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Tensor.SelectMul.eq.MulSelectS
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt
import Lemma.Tensor.SelectSum.as.SumSelect.of.Gt
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Lt.GeLength
import Lemma.Tensor.UnsqueezeCast.as.Unsqueeze.of.Eq
import Lemma.Tensor.UnsqueezeUnsqueeze_0
open Bool Nat Tensor
set_option maxHeartbeats 1000000


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
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEq.of.Eq
    apply EqCastS.of.SEq.Eq (by simp)
    simp
    apply SEq.of.Eq
    congr 1
    erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by grind⟩)]
    simp
    erw [EqGetUnsqueeze_0.fin]
    have h := SelectUnsqueeze.eq.Cast.of.GeLength (s := [n]) (d := 0) (by simp) Y
    simp at h
    simp [h]
    apply Eq.of.SEq
    apply SEqCast.of.SEq.Eq (by simp)
    apply UnsqueezeCast.as.Unsqueeze.of.Eq (by simp)
  ·
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    have h := SelectUnsqueeze.eq.Cast.of.GeLength (s := [m, n]) (d := 1) (by simp) Xᵀ
    simp at h
    apply h.trans
    apply Eq.of.SEq
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEq.of.Eq
    erw [EqGetUnsqueeze_0.fin]


@[main]
private lemma resize
  [CommMagma α] [AddCommMonoid α]
-- given
  (X : Tensor α [n, m])
  (Y : Tensor α [n']) :
-- imply
  Xᵀ @ Y = Y @ X := by
-- proof
  rw [Dot.eq.GetSumMul.resize]
  erw [Dot.eq.SelectSumMul.resize]
  conv_lhs => erw [SelectSum.eq.Cast_SumSelect.of.Gt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
  simp
  erw [GetSum_2.eq.SumGet__1.fin]
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  erw [SelectMul.eq.MulSelectS]
  erw [GetMul.eq.MulGetS.fin]
  rw [Mul.comm]
  apply SEqMulS.of.SEq.SEq
  ·
    erw [SelectCast.eq.Cast_Select.of.Eq (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by grind⟩)]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨0, by grind⟩) (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    erw [UnsqueezeUnsqueeze_0 (Y.resize 0 (n' ⊔ n))]
    erw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    simp
    apply SEqRepeatS.of.SEq.Val.Eq (by simp) (by simp)
    erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by grind⟩)]
    simp
    erw [EqGetUnsqueeze_0.fin]
    have h := SelectUnsqueeze.eq.Cast.of.GeLength (s := [n'].set 0 (n ⊔ n')) (d := 0) (by simp) (Y.resize 0 (n ⊔ n'))
    simp at h
    simp [h]
    apply SEqUnsqueezeS.of.SEq
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEqResizeS.of.SEq.Val.Eq (by rw [Max.comm]) (by simp)
    rfl
  ·
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    have h := SelectUnsqueeze.eq.Cast.of.GeLength (d := 1) (by simp) (Xᵀ.resize ⟨1, by simp⟩ (n ⊔ n'))
    simp at h
    apply (SEq.of.Eq h).trans
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    erw [EqGetUnsqueeze_0.fin]
    have hR : Xᵀ.resize ⟨1, by simp⟩ (n ⊔ n') ≃ Xᵀ.resize ⟨1, by simp⟩ (n' ⊔ n) :=
      SEqResizeS.of.SEq.Val.Eq (by rw [Max.comm]) (by simp) (by rfl)
    apply hR.trans
    apply SEq.of.Eq
    apply ResizeT_1.eq.TResize_0


-- created on 2026-07-30
-- updated on 2026-08-27
