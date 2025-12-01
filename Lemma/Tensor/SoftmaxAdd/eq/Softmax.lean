import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Tensor.DataAdd.eq.AddData
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data.of.GtLength
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.ExpAdd.eq.MulExpS
import Lemma.Tensor.Softmax.eq.One.of.LeLength
import Lemma.Tensor.SumMul.eq.MulSum
import Lemma.Vector.Cast_Mul.eq.MulCast.of.Eq
import Lemma.Vector.ExpAdd.eq.MulExpS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.Mul.eq.Mul_Replicate
import Lemma.Vector.RepeatMul.eq.MulRepeat
import Lemma.Vector.SplitAtMul.eq.MulSplitAt
open Fin List Nat Rat Tensor Vector


@[main]
private lemma main
  [ExpRing α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  (X + δ).softmax d = X.softmax d := by
-- proof
  if h : s.length > d then
    unfold Tensor.softmax
    simp
    apply Eq.of.EqDataS
    simp [DataDiv.eq.DivDataS]
    simp [DataExp.eq.ExpData]
    simp [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data.of.GtLength h]
    simp [DataAdd.eq.AddData]
    simp [@Vector.ExpAdd.eq.MulExpS.scalar]
    simp [@Tensor.ExpAdd.eq.MulExpS.scalar]
    simp [SumMul.eq.MulSum]
    simp [DataMul.eq.MulData]
    rw [Cast_Mul.eq.MulCast.of.Eq]
    ·
      rw [SplitAtMul.eq.MulSplitAt]
      ext t
      have h_t := t.isLt
      simp [GetDiv.eq.DivGetS.fin]
      simp [GetMul.eq.MulGet.fin]
      have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by 
        simp [Mul_Mul.eq.MulMul.comm]
        rw [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
      repeat rw [GetCast.eq.Get.of.Eq.fin h_prod]
      simp only [← h_prod] at h_t
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
      let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
      simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
      simp [GetMul.eq.MulGet.fin]
      simp [← Mul.eq.Mul_Replicate]
      simp [RepeatMul.eq.MulRepeat]
      simp [GetMul.eq.MulGet.fin]
      rw [DivMulS.eq.Div.of.Ne_0]
      apply ExpNeZero.exp_ne_zero
    ·
      rw [ProdInsertIdx.eq.Prod]
  else
    repeat rw [Softmax.eq.One.of.LeLength (by omega)]


-- created on 2025-11-30
-- updated on 2025-12-01
