import Lemma.Fin.Lt0Sum.of.All_Gt_0.Gt_0
import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.List.TakeInsertIdxEraseIdx.eq.Take
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Ne.of.Gt
import Lemma.Real.GtExp_0
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.EqMulDiv.of.All_Ne_0
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.Softmax.eq.One.of.LeLength
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
open Fin List Nat Real Tensor Vector


@[main]
private lemma main
  [ExpPos α]
  [IsOrderedCancelAddMonoid α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  exp X = X.softmax d * ((exp X).sum d).keepdim := by
-- proof
  if h_d : d < s.length then
    rw [Softmax.eq.DivExp_KeepdimSumExp]
    rw [@Tensor.EqMulDiv.of.All_Ne_0.fin]
    intro i
    simp [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h_d⟩)]
    have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by
      rw [ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength h_d]
      rw [TakeInsertIdxEraseIdx.eq.Take]
      simp [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h_d]
    rw [GetCast.eq.Get.of.Eq.fin h_prod]
    have h_i := i.isLt
    simp [← h_prod] at h_i
    let type := List.Vector
      (List.Vector α (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod))
      (((s.eraseIdx d).insertIdx d 1).take d).prod
    let ⟨q, r, h_qr⟩ := Any_EqAddMul.of.Lt_Mul h_i
    simp [← h_qr]
    simp [GetFlatten_AddMul.eq.Get.fin]
    rw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
    simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    rw [GetCast.eq.Get.of.Eq.fin]
    ·
      simp
      rw [DataSum.eq.Sum_DataSelect (d := ⟨d, h_d⟩)]
      apply Ne.of.Gt
      rw [GetSum.eq.Sum_Get.fin]
      apply Lt0Sum.of.All_Gt_0.Gt_0
      ·
        grind
      ·
        intro i
        have h_i := i.isLt
        conv_rhs at h_i => simp
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        rw [GetCast.eq.Get.of.Eq.fin]
        ·
          have h_q := q.isLt
          have h_r := r.isLt
          simp [ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength h_d] at ⊢ h_r
          simp [TakeInsertIdxEraseIdx.eq.Take] at h_q
          have := GetFlatten_AddMul.eq.Get.fin
            (((exp X).data.splitAt (d + 1)).getSlice ⟨↑↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩)
            ⟨q, by rwa [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp h_d h_i]⟩
            ⟨r % (s.drop (d + 1)).prod, by apply LtMod.of.Gt_0 (by grind)⟩
          simp at this
          rw [this]
          rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ h_i]
          ·
            simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [DataExp.eq.ExpData]
            rw [GetExp.eq.ExpGet.fin]
            apply GtExp_0
          ·
            apply Get.dvd.ProdTake.of.GtLength
          ·
            rwa [DivProdTake.eq.ProdTake.of.Ne_0.GtLength]
            grind
        ·
          have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength.simp h_d h_i
          simp at this
          simp [this]
    ·
      simp [ProdInsertIdx.eq.Prod]
  else
    simp at h_d
    simp [Softmax.eq.One.of.LeLength h_d]
    rw [Sum.eq.Cast_Sum.of.LeLength h_d]
    simp [Keepdim.eq.Cast.of.LeLength h_d]


-- created on 2025-12-30
-- updated on 2026-01-02
