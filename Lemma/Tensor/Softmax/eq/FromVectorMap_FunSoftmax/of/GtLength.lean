import Lemma.Finset.Sum.of.All_Eq.Eq
import Lemma.List.Get.dvd.Mul_ProdTake.of.GtLength
import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.List.LengthSlice.eq.Div.of.Lt.Dvd
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdDrop.dvd.Prod
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.List.TakeEraseIdx.eq.Take
import Lemma.List.TakeInsertIdx.eq.Take
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.AddMulDiv_Mul
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Nat.DivMul.eq.Mul_Div.of.Dvd
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.ModMod.eq.Mod.of.Dvd
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
open Finset List Nat Tensor Vector Fin


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
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
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
  rw [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d + 1, by grind⟩)]
  rw [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, by grind⟩)]
  simp
  have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by
    simp [Mul_Mul.eq.MulMul.comm]
    apply MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
  repeat rw [GetCast.eq.Get.of.Eq.fin (by grind)]
  have h_lt : t < n * (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) := by
    simp [Mul_Mul.eq.MulMul.comm]
    simp [MulMul.eq.Mul_Mul]
    rwa [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
  let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
  let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
  have h_q' := q'.isLt
  have h_r' := r'.isLt
  have h_lt : r < (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) := by
    simp [Mul_Mul.eq.MulMul.comm]
    rwa [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
  have h_qₐ := qₐ.isLt
  simp [TakeInsertIdx.eq.Take, TakeEraseIdx.eq.Take] at h_q' h_qₐ
  have h_rₐ := rₐ.isLt
  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
  simp
  repeat rw [GetRepeat.eq.Get_Mod.fin]
  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp [ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength h] at ⊢ h_rₐ h_q'_div h_r'_mod h_qₐ_div h_rₐ_mod
  rw [DataSum.eq.Sum_DataSelect (d := ⟨d + 1, by grind⟩)]
  rw [DataSum.eq.Sum_DataSelect (d := ⟨d, by grind⟩)]
  have h_prod : (s.eraseIdx d).prod = ((s.eraseIdx d).insertIdx d 1).prod := by
    simp [ProdInsertIdx.eq.Prod]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by grind)]
  repeat rw [GetSum.eq.Sum_Get.fin]
  simp
  apply Sum.of.All_Eq.Eq (by simp)
  intro k
  have h_k := k.isLt
  repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
  repeat rw [GetCast.eq.Get.of.Eq.fin]
  ·
    have h_dvdₑ := Get.dvd.Mul_ProdTake.of.GtLength h n
    have h_dvdₕ := Get.dvd.ProdTake.of.GtLength h
    have h_lt : ↑q' * (s.drop (d + 1)).prod + ↑r' % (s.drop (d + 1)).prod < (⟨↑↑k, ↑(n * (s.take (d + 1)).prod), ↑s[d]⟩ : Slice).length (n * (s.take (d + 1)).prod) * (s.drop (d + 1)).prod := by
      rw [LengthSlice.eq.Div.of.Lt.Dvd h_dvdₑ h_k]
      rw [DivMul.eq.Mul_Div.of.Dvd h_dvdₕ]
      rw [DivProdTake.eq.ProdTake.of.Ne_0.GtLength h (by grind)]
      apply AddMul.lt.Mul.of.Lt.Lt h_q'
      apply LtMod.of.Ne_0
      grind
    let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
    let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
    have h_qₑ := qₑ.isLt
    simp only [LengthSlice.eq.Div.of.Lt.Dvd h_dvdₑ h_k] at h_qₑ
    have h_rₑ := rₑ.isLt
    have h_lt : ↑qₐ * (s.drop (d + 1)).prod + ↑rₐ % (s.drop (d + 1)).prod < (⟨↑↑k, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
      rw [LengthSlice.eq.Div.of.Lt.Dvd h_dvdₕ h_k]
      rw [DivProdTake.eq.ProdTake.of.Ne_0.GtLength h (by grind)]
      apply AddMul.lt.Mul.of.Lt.Lt h_qₐ
      apply LtMod.of.Ne_0
      grind
    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
    let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
    have h_qₕ := qₕ.isLt
    simp only [LengthSlice.eq.Div.of.Lt.Dvd h_dvdₕ h_k] at h_qₕ
    have h_rₕ := rₕ.isLt
    repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
    repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
    ·
      simp [DataExp.eq.ExpData]
      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      rw [GetExp.eq.ExpGet.fin]
      rw [GetExp.eq.ExpGet.fin]
      rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      repeat apply congrArg
      simp
      simp [MulAdd.eq.AddMulS]
      simp [Add_Add.eq.AddAdd]
      rw [AddAdd.comm]
      conv_rhs => rw [AddAdd.comm]
      simp
      simp at h_rₕ_mod h_rₑ_mod
      rw [DivAddMul.eq.Add_Div.of.Ne_0 (by grind)] at h_qₕ_div h_qₑ_div
      simp at h_qₕ_div h_qₑ_div
      simp [h_qₕ_div, h_qₑ_div, h_rₕ_mod, h_rₑ_mod]
      simp [h_r'_mod, h_rₐ_mod, h_r_mod]
      rw [ModMod.eq.Mod.of.Dvd (by apply ProdDrop.dvd.Prod)]
      simp [MulMul.eq.Mul_Mul]
      rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h] at ⊢ h_qₐ_div h_q'_div
      simp only [Prod.eq.MulProdS s d] at ⊢ h_q_div h_r_mod
      rw [Mul_Mul.eq.MulMul]
      simp [AddMulS.eq.MulAdd]
      left
      rw [h_qₐ_div, h_q'_div, h_q_div, h_r_mod]
      apply Div.eq.AddMulDiv_Mul
    ·
      simpa
    ·
      simpa
    ·
      simp
    ·
      simpa
    ·
      exact h_qₑ
    ·
      simp
  ·
    have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength.simp (by grind) (by grind) (s := s) (d := d) (i := k)
    simp_all
  ·
    have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength.simp (by grind) (by grind) (s := n :: s) (d := d + 1) (i := k)
    simp_all


-- created on 2025-11-29
-- updated on 2025-11-30
