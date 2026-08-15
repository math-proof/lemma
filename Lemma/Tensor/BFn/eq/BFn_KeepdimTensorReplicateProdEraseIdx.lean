import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.NotLt.is.Ge
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataKeepdim.as.FlattenMapSplitAtCast_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Fin List Nat Tensor Vector


@[main]
private lemma main
  {f : α → α → α}
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  X.map (f · δ) =
    X.map₂ f (⟨List.Vector.replicate (s.eraseIdx d).prod δ⟩ : Tensor α (s.eraseIdx d)).keepdim := by
-- proof
  if h : s.length > d then
    apply Eq.of.EqDataS
    simp only [Tensor.map, Tensor.map₂]
    rw [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h⟩)]
    ext t
    have h_t := t.isLt
    simp
    congr 1
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
      simp
    ·
      rw [ProdInsertIdx.eq.Prod]
  else
    have h := Le.of.NotGt h
    rw [Keepdim.eq.Cast.of.LeLength h]
    have h_s := EqEraseIdx.of.LeLength h
    apply Eq.of.EqDataS
    simp only [Tensor.map, Tensor.map₂]
    ext t
    simp
    congr 1
    rw [DataCast.eq.Cast_Data.of.Eq h_s]
    rw [GetCast.eq.Get.of.Eq.fin]
    ·
      simp
    ·
      rw [h_s]


-- created on 2026-08-15
