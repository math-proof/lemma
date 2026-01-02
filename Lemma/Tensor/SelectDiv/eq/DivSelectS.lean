import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne_0
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector Fin


@[main]
private lemma main
  [Div α]
-- given
  (A B : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (A / B).select d i = A.select d i / B.select d i := by
-- proof
  simp [HDiv.hDiv]
  apply Eq.of.EqDataS
  rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
  have h_length_slice := MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s) (i := i) (d := d) (by simp) (by simp)
  apply EqCast.of.SEq.Eq (by simp [h_length_slice])
  simp [Div.div]
  apply SEq.of.All_EqGetS.Eq.fin (by simp [h_length_slice])
  intro t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  have h_q := q.isLt
  simp at h_q
  rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength d.isLt i.isLt] at h_q
  rw [ProdTake.eq.DivProdTake.of.Ne_0.GtLength d.isLt (Ne_0 i)] at h_q
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd (by simp) (by assumption) (by simp)]
  rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  repeat rw [GetDiv.eq.DivGetS.fin]
  repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by simp [h_length_slice])]
  simp
  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd (by simp) (by assumption) (by simp)]
  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]


-- created on 2025-11-17
