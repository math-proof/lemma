import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDotDot.eq.DotDotGet
import Lemma.Tensor.GetDot_Dot.eq.Dot_Dot_GetT
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.SEqSelectUnsqueeze.of.GeLength
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Tensor.SelectMul.eq.MulSelectS
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt
import Lemma.Tensor.SelectSum.as.SumSelect.of.Gt
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Lt.GeLength
import Lemma.Tensor.Select_0.as.Get.of.GtLength_0
open Bool Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma vec
  [NonUnitalSemiring α]
  -- [CommMagma α] [Add α] [Zero α]
-- given
  (L : Tensor α [m])
  (M : Tensor α [m, n])
  (N : Tensor α [n]) :
-- imply
  (L @ M) @ N = L @ (M @ N) := by
-- proof
  apply (Dot.eq.SumMul__0 (L @ M) N).trans
  symm
  apply (Dot.eq.SumMul__0 L (M @ N)).trans
  rw [Dot.eq.GetSumMul]
  rw [Dot.eq.SelectSumMul]
  rw [SelectSum.eq.Cast_SumSelect.of.Gt (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩) (by grind)]
  simp
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨0, by grind⟩)]
  simp
  rw [GetMul.eq.MulGetS.fin]
  rw [SelectMul.eq.MulSelectS]
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 2
    erw [SelectCast.eq.Cast_Select.of.Eq (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
  simp
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 2
    arg 2
    erw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by grind) (d := ⟨1, by grind⟩) (i := ⟨0, by simp⟩)]
  simp
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 2
    arg 2
    arg 1
    erw [SelectUnsqueeze.eq.Cast_UnsqueezeSelect.of.Lt.GeLength (by grind) (by grind) (i := ⟨0, by simp⟩)]
  simp
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 2
    arg 2
    arg 1
    arg 1
    erw [Select_0.eq.Cast_Get.of.GtLength_0 (by grind)]
  simp
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 2
    arg 2
    arg 1
    arg 1
    erw [EqGetUnsqueeze_0.fin]
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    arg 1
    erw [SelectUnsqueeze.eq.Cast.of.GeLength (by grind)]
  simp
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 1
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨0, by grind⟩) (s' := [1, n, m]) (by grind) (by grind)]
  simp
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 1
    arg 2
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
  simp
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 1
    arg 2
    arg 1
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
  simp
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 1
    arg 2
    arg 1
    arg 1
    erw [EqGetUnsqueeze_0.fin]
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 2
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
  simp
  conv_rhs =>
    arg 1
    arg 1
    arg 1
    arg 2
    erw [EqGetUnsqueeze_0.fin]
  -- apply Eq.of.SEq
  -- apply SEqSumS.of.SEq
  sorry


/--
tensor version of Matrix.mul_assoc
-/
@[main]
private lemma main
  -- [NonUnitalSemiring α]
  [CommMagma α] [Add α] [Zero α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o]) :
-- imply
  (L @ M) @ N = L @ (M @ N) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (GetDotDot.eq.DotDotGet L M N i j).trans
  symm
  apply (GetDot_Dot.eq.Dot_Dot_GetT L M N i j).trans
  have := vec L[i] M Nᵀ[j]
  simp at this
  simp
  conv_rhs => erw [this]
  rfl


-- created on 2025-05-03
-- updated on 2026-07-21
