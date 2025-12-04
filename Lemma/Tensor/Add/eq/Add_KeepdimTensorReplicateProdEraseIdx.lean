import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.NotGt.is.Le
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Fin List Nat Tensor Vector


@[main]
private lemma main
  [Add α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  X + δ = X + (⟨List.Vector.replicate (s.eraseIdx d).prod δ⟩ : Tensor α (s.eraseIdx d)).keepdim := by
-- proof
  if h : s.length > d then
    conv_lhs => simp [HAdd.hAdd]
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h⟩)]
    ext t
    have h_t := t.isLt
    simp
    rw [GetAdd.eq.AddGetS.fin]
    have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by
      simp [Mul_Mul.eq.MulMul.comm]
      rw [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
    rw [GetCast.eq.Get.of.Eq.fin h_prod]
    simp only [← h_prod] at h_t
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    simp [GetRepeat.eq.Get_Mod.fin]
    simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    rw [GetCast.eq.Get.of.Eq.fin]
    ·
      simp [HAdd.hAdd]
    ·
      rw [ProdInsertIdx.eq.Prod]
  else
    have h := Le.of.NotGt h
    rw [Keepdim.eq.Cast.of.LeLength h]
    have h_s := EqEraseIdx.of.LeLength h
    conv_lhs => simp [HAdd.hAdd]
    apply Eq.of.EqDataS
    simp [DataAdd.eq.AddDataS]
    ext t
    rw [GetAdd.eq.AddGetS.fin]
    rw [DataCast.eq.Cast_Data.of.Eq h_s]
    rw [GetCast.eq.Get.of.Eq.fin]
    .
      simp [HAdd.hAdd]
    .
      rw [h_s]


-- created on 2025-12-04
