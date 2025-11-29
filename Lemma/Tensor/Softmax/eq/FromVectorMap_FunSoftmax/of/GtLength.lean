import Lemma.Finset.Sum.of.All_Eq.Eq
import Lemma.List.EqGetS
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdDropInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.DataUnsqueeze.eq.Map_FunGetData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
import sympy.tensor.functions
open List Finset Nat Tensor Vector
set_option maxHeartbeats 2000000


@[main]
private lemma main
  [Exp α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s)) :
-- imply
  X.softmax (d + 1) = Tensor.fromVector (X.toVector.map (·.softmax d)) := by
-- proof
  obtain ⟨X⟩ := X
  unfold Tensor.softmax Tensor.fromVector
  simp
  apply Eq.of.EqDataS
  simp [DataDiv.eq.DivDataS]
  ext t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
  have h_q := q.isLt
  have h_r := r.isLt
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  simp
  repeat rw [GetDiv.eq.DivGetS.fin]
  unfold Tensor.toVector
  simp [DataExp.eq.ExpData]
  rw [GetCast.eq.Get.of.Eq.fin (by simp)]
  simp [GetExp.eq.ExpGet.fin]
  rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp [← h_qr]
  apply EqDivS.of.Eq.left
  unfold Tensor.keepdim
  simp [h]
  repeat rw [DataCast.eq.Cast_Data.of.Eq (by simp [EqSetInsertIdxEraseIdx.of.GtLength])]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by simp [EqSetInsertIdxEraseIdx.of.GtLength])]
  repeat rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
  simp
  have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = (((s.eraseIdx d).insertIdx d 1).set d (s[d] * ((s.eraseIdx d).insertIdx d 1)[d]'(by grind))).prod := by
    simp
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
    simp [Mul_Mul.eq.MulMul.comm]
    apply MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
  repeat rw [GetCast.eq.Get.of.Eq.fin (by grind)]
  simp
  have h_lt : t < n * (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) := by
    simp [Mul_Mul.eq.MulMul.comm]
    simp [MulMul.eq.Mul_Mul]
    rwa [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
  let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
  let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
  have h_q' := q'.isLt
  have h_r' := r'.isLt
  have h_lt : r < (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) := by
    simp [Mul_Mul.eq.MulMul.comm]
    rwa [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
  have h_qₐ := qₐ.isLt
  have h_rₐ := rₐ.isLt
  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
  simp
  repeat rw [GetRepeat.eq.Get_Mod.fin]
  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp [ProdDropInsertIdxEraseIdx.eq.Prod.of.GtLength h]
  repeat rw [DataUnsqueeze.eq.Map_FunGetData.fin]
  simp
  simp [EqGetRange.fin]
  rw [DataSum.eq.Sum_DataSelect (d := ⟨d + 1, by grind⟩)]
  rw [DataSum.eq.Sum_DataSelect (d := ⟨d, by grind⟩)]
  repeat rw [GetSum.eq.Sum_Get.fin]
  apply Sum.of.All_Eq.Eq
  ·
    intro k
    have h_k := k.isLt
    have := GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (i := d + 1) (show d + 1 > 0 by omega) (show d + 1 < s.length + 1 by omega) n
    simp only [EqSubAdd] at this
    simp only [GetElem.getElem] at this
    simp only [GetElem.getElem] at h_k
    simp only [this] at h_k
    simp only [@List.EqGetS] at h_k
    repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
    repeat rw [GetCast.eq.Get.of.Eq.fin]
    .
      sorry
    .
      sorry
    .
      sorry
  ·
    sorry


-- created on 2025-11-29
