import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetTranspose.eq.Get
open Bool List Tensor
set_option maxHeartbeats 10000000


@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n)
  (k : Fin l) :
-- imply
  (((cast (congrArg (Tensor α) (show ([] ++ [1, n, l]).set 0 (m * ([] ++ [1, n, l])[0]) = [] ++ [m, n, l] by grind)) (((cast (congrArg (Tensor α) (show ([] ++ [l, n]).swap (([] ++ [l, n]).length - 2) (([] ++ [l, n]).length - 1) = [] ++ [n, l] by simp [EqSwap_0'1])) Bᵀ).unsqueeze 0).repeat (0 : Fin 3) m)).get i).get j).get k = (B.get k).get j := by
-- proof
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) (by simp) (i := ⟨i, by simp⟩)]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp) (i := ⟨j, by simp⟩)]
  simp
  erw [GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
  simp
  erw [EqGetUnsqueeze_0.nat.fin]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp [EqSwap_0'1]) (by simp [EqSwap_0'1]) (i := ⟨j, by simp [EqSwap_0'1]⟩)]
  simp
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp [EqSwap_0'1]) (by simp [EqSwap_0'1]) (i := ⟨k, by simp [EqSwap_0'1]⟩)]
  simp
  apply EqCast.of.SEq
  apply SEq.of.Eq
  apply GetTranspose.eq.Get.fin B


-- created on 2026-07-09
