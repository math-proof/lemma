import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.GtLength
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
-- given
  (d : Fin s.length)
  (i : Fin s[d])
  (a : α) :
-- imply
  (⟨List.Vector.replicate s.prod a⟩ : Tensor α s).select d i = ⟨List.Vector.replicate (s.eraseIdx d).prod a⟩ := by
-- proof
  have h_i := i.isLt
  apply Eq.of.EqDataS
  simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
  have h_length_slice : (⟨↑↑i, ↑(s.take (↑d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (↑d + 1)).prod * (s.drop (↑d + 1)).prod = (s.eraseIdx ↑d).prod := by 
    simp
    rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
    grind
  apply EqCast.of.SEq.Eq h_length_slice
  apply SEq.of.All_EqGetS.Eq.fin h_length_slice
  intro t
  have h_t := t.isLt
  simp
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  have h_q := q.isLt
  simp at h_q
  rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength d.isLt h_i] at h_q
  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
  have h_prod := ProdTake.eq.Mul_ProdTake.of.GtLength d.isLt
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin]
  ·
    simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  ·
    simp [h_prod]
  ·
    simp [h_prod]
    rwa [EqDivMul.of.Ne_0.left (by grind)]
  ·
    exact i.isLt


-- created on 2025-12-01
