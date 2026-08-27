import Lemma.Bool.Cast.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Tensor.DataOfVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataResize.as.FlattenMapSplitAtData
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.Get_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.Tensordot.of.SEq.SEq
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Resize.as.OfVectorMapToVector.of.GtVal_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Nat Tensor Vector
set_option maxHeartbeats 500000


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
  have hmax : k ⊔ n' = n' := EqMax.of.Lt h
  unfold Tensor.resize
  simp [Dot.dot]
  conv_rhs => rw [Einsum.eq.Cast_Tensordot.of.Get_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simp)]
  rw [Einsum.eq.Cast_Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp)]
  apply Cast.of.SEq.Eq
  ·
    simp [broadcast_shape, matmul_shape]
  ·
    simp
    erw [hmax]
    rw [Resize.eq.Cast_OfVectorMapToVector.of.GtVal_0 _ (by simp)]
    simp
    apply SEq.of.Eq
    apply Tensordot.of.SEq.SEq
    .
      apply SEq.of.SEqDataS.Eq
      ·
        simp
      ·
        simp
        apply SEq_Cast.of.SEq.Eq (by simp)
        apply SEq.of.All_EqGetS.Eq.fin (by simp)
        intro t
        have h_t := t.isLt
        erw [DataOfVector.eq.FlattenMapData]
        repeat erw [GetFlatten.eq.Get.of.Lt_Mul (by grind)]
        rw [GetMap.eq.UFnGet]
        conv_rhs => erw [GetMap.eq.UFnGet]
        conv_lhs => erw [GetMap.eq.UFnGet]
        simp
        have h_t' : t < X.length * n' := by simpa [Tensor.length] using h_t
        have h_div := LtDiv.of.Lt_Mul h_t'
        have h_mod := LtMod.of.Lt_Mul h_t'
        erw [GetToVector.eq.Get.fin (i := ⟨t / n', h_div⟩)]
        erw [DataResize.eq.Cast_FlattenMapSplitAtData]
        erw [GetCast.eq.Get.of.Eq.fin (by simp)]
        simp
        rw [GetResize.eq.Ite_Get_Mod.fin]
        simp
        split_ifs with h_it
        ·
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          erw [GetFlatten.eq.Get.of.Lt_Mul (by simp [h_mod])]
          simp
          erw [GetResize.eq.Ite_Get_Mod.fin]
          split_ifs with h_it'
          ·
            simp
            erw [GetCast.eq.Get.of.Eq.fin (by simp)]
            erw [GetArraySlice.eq.Get_Add.of.Lt_Min_Sub.fin (by simp; apply Nat.mod_lt; grind)]
            simp
            erw [GetCast.eq.Get.of.Eq.fin (by simp)]
            erw [DataGet.eq.GetUnflattenData.fin]
            erw [GetUnflatten.eq.Get_AddMul.fin]
            simp
          ·
            grind
        ·
          obtain h_eq | h_lt := Nat.eq_or_lt_of_le (Nat.div_mul_le_self n' k)
          ·
            grind
          ·
            erw [GetFlatten.eq.Get.of.Lt_Mul (by grind)]
            erw [GetMap.eq.UFnGet]
            erw [GetResize.eq.Ite_Get_Mod.fin]
            simp
            grind
    ·
      apply SEqResize.of.Eq_Get (i := ⟨0, by grind⟩)
      simp


-- created on 2026-07-10
-- updated on 2026-08-27
