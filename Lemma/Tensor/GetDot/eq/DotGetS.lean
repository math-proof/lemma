import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulS.of.Eq.Eq
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.EqGetS.of.Eq
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.GtLength_0
open Nat Tensor
set_option maxHeartbeats 1000000


/--
tensor version of Matrix.mul_apply
-/
@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = A[i] @ Bᵀ[j] := by
-- proof
  rw [Dot.eq.SumMul]
  let Ai : Tensor α [k] := A[i]
  let Bj : Tensor α [k] := Bᵀ[j]
  have := Dot.eq.SumMul__0 Ai Bj
  simp [Ai, Bj] at this
  erw [this]
  simp [GetElem.getElem]
  erw [GetSum_2.eq.SumGet__0.fin]
  apply EqSumS.of.Eq
  rw [GetMul.eq.MulGetS.fin]
  conv_lhs => erw [GetMul.eq.MulGetS.fin]
  apply EqMulS.of.Eq.Eq
  ·
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨i, by grind⟩) (s' := [m, n, k]) (by grind) (by grind)]
    simp
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨j, by grind⟩) (s' := [m, n, k].tail) (by grind) (by grind)]
    simp
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    simp
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    simp [EqMod_1'0]
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.GtLength_0.fin (by grind) (by grind)]
    simp
    apply EqGetUnsqueeze_0
  ·
    apply EqGetS.of.Eq
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨i, by grind⟩) (s' := [m, n, k]) (by grind) (by grind)]
    simp
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    simp [EqMod_1'0]
    apply EqGetUnsqueeze_0


-- created on 2025-06-22
-- updated on 2026-07-21
