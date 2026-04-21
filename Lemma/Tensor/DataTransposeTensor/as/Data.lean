import Lemma.Vector.Head.eq.Get_0
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_0
import Lemma.List.EqPermute__0
import Lemma.List.EqSwap_0'1
import Lemma.List.LengthSlice.eq.Min
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.TailPermute__Neg.eq.EraseIdx
import Lemma.Nat.EqMod.of.Lt
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.GetData.eq.GetDataGet.of.GtProd.GtLength_0
import Lemma.Tensor.GetGetSlice.eq.Get
import Lemma.Tensor.GetPermuteTail.eq.Cast_Select.of.Lt_Get.GtLength_0
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Tensor.Permute__Neg.eq.Cast_PermuteTail.of.Val.eq.SubLength_1
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Fin List Nat Tensor Vector


@[main]
private lemma main
-- given
  (v : List.Vector α n) :
-- imply
  (⟨cast (congrArg (List.Vector α) (by simp)) v⟩ : Tensor α [n, 1])ᵀ.data ≃ v := by
-- proof
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    conv_rhs at h_t =>
      simp
    simp [EqSwap_0'1] at h_t
    unfold Tensor.T
    unfold Tensor.transpose
    simp
    rw [Permute__0.eq.Cast]
    have h_permute := EqPermute__0 (0 : Fin (1 + 1)) (s := [n, 1])
    have := GetData.eq.GetDataGet.of.GtProd.GtLength_0.fin (i := t.val) (α := α) (s := (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)))
    simp at this
    rw [this]
    ·
      have h_tail_permute := TailPermute__Neg.eq.EraseIdx (d := ⟨1, by grind⟩) (s := ([n, 1].permute (0 : Fin (1 + 1)) 0))
      simp at h_tail_permute
      have h_t : ↑t % (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = t := by
        rw [h_tail_permute]
        simp [h_permute]
        apply EqMod.of.Lt h_t
      simp [h_t]
      have h_0 : ↑t / (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = 0 := by
        simp
        right
        rw [h_tail_permute]
        simpa [h_permute]
      simp [h_0]
      have h_prod : n = [n, 1].prod := by simp
      have := Permute__Neg.eq.Cast_PermuteTail.of.Val.eq.SubLength_1 (by grind) (⟨cast (congrArg (List.Vector α) h_prod) v⟩ : Tensor α [n, 1]) (i := ⟨1, by grind⟩) (d := 1)
      simp at this
      rw [this]
      have := GetPermuteTail.eq.Cast_Select.of.Lt_Get.GtLength_0 (by grind) (by grind) (⟨cast (congrArg (List.Vector α) h_prod) v⟩ : Tensor α [n, 1]) (k := 0)
      simp at this
      rw [this]
      simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp
        have h_t : t < ((⟨0, ↑n * 1, 1⟩ : Slice).length (n * 1)) * 1 := by
          simpa [LengthSlice.eq.Min]
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        have h_r := Eq_0 r
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        simp [h_r] at h_qr
        rw [GetGetSlice.eq.Get.length_slice.one.fin]
        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        rw [GetCast.eq.Get.of.Eq.fin (by simp)]
        simp [h_qr]
      ·
        simp [LengthSlice.eq.Min]
        simpa [TailPermute__Neg.eq.EraseIdx]
    ·
      rw [ProdPermute.eq.Prod]
      grind
  ·
    simp [EqSwap_0'1]


@[main]
private lemma row
-- given
  (v : List.Vector α n) :
-- imply
  (⟨cast (congrArg (List.Vector α) (by simp)) v⟩ : Tensor α [1, n])ᵀ.data ≃ v := by
-- proof
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    conv_rhs at h_t =>
      simp
    simp [EqSwap_0'1] at h_t
    unfold Tensor.T
    unfold Tensor.transpose
    simp
    rw [Permute__0.eq.Cast]
    have h_permute := EqPermute__0 (0 : Fin (1 + 1)) (s := [1, n])
    have := GetData.eq.GetDataGet.of.GtProd.GtLength_0.fin (i := t.val) (α := α) (s := (([1, n].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)))
    simp at this
    rw [this]
    ·
      have h_tail_permute := TailPermute__Neg.eq.EraseIdx (d := ⟨1, by grind⟩) (s := ([1, n].permute (0 : Fin (1 + 1)) 0))
      simp at h_tail_permute
      have h_t : ↑t % (([1, n].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = 0 := by
        rw [h_tail_permute]
        simp [h_permute]
        omega
      simp only [h_t]
      have h_1 : ↑t / (([1, n].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = t := by
        rw [h_tail_permute]
        simp [h_permute]
      simp [h_1]
      have h_prod : n = [1, n].prod := by simp
      have := Permute__Neg.eq.Cast_PermuteTail.of.Val.eq.SubLength_1 (by grind) (⟨cast (congrArg (List.Vector α) h_prod) v⟩ : Tensor α [1, n]) (i := ⟨1, by grind⟩) (d := 1)
      simp at this
      rw [this]
      have := GetPermuteTail.eq.Cast_Select.of.Lt_Get.GtLength_0 (by grind) (by grind) (⟨cast (congrArg (List.Vector α) h_prod) v⟩ : Tensor α [1, n]) (k := t)
      simp at this
      rw [this]
      simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
      rw [Vector.Head.eq.Get_0.fin]
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp
        have h_t : 0 < ((⟨t, 1 * (↑n * 1), n⟩ : Slice).length (1 * (n * 1))) * 1 := by
          simp
          rw [List.LengthSlice.eq.One.of.Lt (by assumption)]
          simp
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        have h_r := Eq_0 r
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        simp [h_r] at h_qr
        symm at h_qr
        rw [GetGetSlice.eq.Get.length_slice.one.fin]
        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        rw [GetCast.eq.Get.of.Eq.fin (by simp)]
        simp [h_qr]
      ·
        simp
        rwa [List.LengthSlice.eq.One.of.Lt]
    ·
      rw [ProdPermute.eq.Prod]
      grind
  ·
    simp [EqSwap_0'1]


-- created on 2026-04-07
-- updated on 2026-04-21
