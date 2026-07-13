import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.EqGetS.of.Eq
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
open Nat Tensor
set_option maxHeartbeats 4000000


@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (i : Fin m)
  (j : Fin n)
  (k : Fin l) :
-- imply
  (((cast (congrArg (Tensor α) (show ([] ++ [m, 1, l]).set 1 (n * ([] ++ [m, 1, l])[1]) = [] ++ [m, n, l] by grind)) ((A.unsqueeze 1).repeat (1 : Fin 3) n)).get i).get j).get k = (A.get i).get k := by
-- proof
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) (by simp) (i := ⟨i, by simp⟩)]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp) (i := ⟨j, by simp⟩)]
  simp
  apply EqGetS.of.Eq.fin
  erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (i := i) (by simp) (by simp)]
  simp
  erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
  simp [EqMod_1'0]
  erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by simp) (by simp) (by grind)]
  simp
  erw [EqGetUnsqueeze_0.fin]


-- created on 2026-07-09
