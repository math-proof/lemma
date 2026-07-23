import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataResize.as.FlattenMapSplitAtData
import Lemma.Tensor.Einsum.as.Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqTensordotS.of.SEq.SEq
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Resize.as.FromVectorMapToVector.of.GtVal_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k']) :
-- imply
  X @ Y = (X.resize ⟨1, by grind⟩ n') @ Y := by
-- proof
  unfold Tensor.resize
  simp [Dot.dot]
  conv_rhs => rw [Einsum.eq.Cast_Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simp)]
  rw [Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
  apply EqCastS.of.SEq.Eq
  ·
    simp [broadcast_shape, matmul_shape]
  ·
    simp
    rw [Resize.eq.Cast_FromVectorMapToVector.of.GtVal_0 _ (by simp)]
    simp
    apply SEq.of.Eq
    apply EqTensordotS.of.SEq.SEq _ (by rfl)
    apply SEq.of.SEqDataS.Eq
    ·
      simp
    ·
      simp
      apply SEq_Cast.of.SEq.Eq (by simp)
      apply SEq.of.All_EqGetS.Eq.fin (by simp)
      intro t
      have h_t := t.isLt
      rw [DataFromVector.eq.FlattenMapData]
      repeat erw [GetFlatten.eq.Get.of.Lt_Mul (by grind)]
      simp
      have h_t' : t < X.length * n' := by simpa [Tensor.length] using h_t
      have h_div := LtDiv.of.Lt_Mul h_t'
      have h_mod := LtMod.of.Lt_Mul h_t'
      erw [GetToVector.eq.Get.fin (i := ⟨t / n', h_div⟩)]
      simp [DataResize.eq.Cast_FlattenMapSplitAtData]
      rw [GetCast.eq.Get.of.Eq.fin (by simp)]
      simp
      rw [GetResize.eq.Ite_Get_Mod.fin]
      simp
      split_ifs with h_it
      ·
        erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        erw [GetFlatten.eq.Get.of.Lt_Mul (by simp [h_mod])]
        simp
        rw [GetResize.eq.Ite_Get_Mod.fin]
        split_ifs with h_it'
        ·
          rw [Head.eq.Get_0.fin]
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨t / n', h_div⟩) (by grind)]
          simp
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          congr 1
          simp
        ·
          grind
      ·
        obtain h_eq | h_lt := Nat.eq_or_lt_of_le (Nat.div_mul_le_self n' k)
        ·
          grind
        ·
          erw [GetFlatten.eq.Get.of.Lt_Mul (by grind)]
          simp [GetResize.eq.Ite_Get_Mod.fin]
          grind


-- created on 2026-07-10
-- updated on 2026-07-13
