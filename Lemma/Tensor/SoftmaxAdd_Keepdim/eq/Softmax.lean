import Def.Data.Holor.Prod
import Lemma.List.ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength
import Lemma.List.TakeInsertIdxEraseIdx.eq.Take
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Tensor.DataKeepdim.as.FlattenMapSplitAtCast_Data
import Lemma.Tensor.ExpAdd.eq.MulExpS
import Lemma.Tensor.KeepdimExp.eq.ExpKeepdim
import Lemma.Tensor.Softmax.eq.One.of.LeLength
import Lemma.Tensor.SumMul_Keepdim.eq.MulSum
import Lemma.Vector.RepeatMul.eq.MulRepeatS
open Fin List Nat Rat Tensor Vector


@[path]
private lemma main
  [ExpRing α]
  {d : ℕ}
-- given
  (X : Tensor α s)
  (δ : Tensor α (s.eraseIdx d)) :
-- imply
  (X + δ.keepdim).softmax d = X.softmax d := by
-- proof
  if h : s.length > d then
    unfold Tensor.softmax
    simp
    apply Eq.of.EqDataS
    simp [DataDiv.eq.DivDataS]
    simp [DataExp.eq.ExpData]
    simp [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h⟩)]
    simp [DataAdd.eq.AddDataS]
    simp [@Vector.ExpAdd.eq.MulExpS]
    simp [@Tensor.ExpAdd.eq.MulExpS]
    simp [ExpKeepdim.eq.KeepdimExp]
    simp [SumMul_Keepdim.eq.MulSum]
    simp [DataMul.eq.MulDataS]
    rw [@Vector.Cast_Mul.eq.MulCastS.of.Eq]
    ·
      rw [SplitAtMul.eq.MulSplitAtS]
      ext t
      have h_t := t.isLt
      simp [GetDiv.eq.DivGetS.fin]
      simp [@Vector.GetMul.eq.MulGetS.fin]
      have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by
        simp [Mul_Mul.eq.MulMul.comm]
        rw [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength]
      repeat rw [GetCast.eq.Get.of.Eq.fin h_prod]
      simp only [← h_prod] at h_t
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
      simp [DataExp.eq.ExpData]
      simp [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h⟩)]
      simp [GetExp.eq.ExpGet.fin]
      rw [GetCast.eq.Get.of.Eq.fin h_prod]
      simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
      simp [@Vector.GetMul.eq.MulGetS.fin]
      simp [RepeatMul.eq.MulRepeatS]
      simp [@Vector.GetMul.eq.MulGetS.fin]
      simp [GetRepeat.eq.Get_Mod.fin]
      simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      repeat rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp [ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength h]
        simp [GetExp.eq.ExpGet.fin]
        rw [DivMulS.eq.Div.of.Ne_0]
        apply Real.NeExp_0
      repeat rw [ProdInsertIdx.eq.Prod]
    ·
      rw [ProdInsertIdx.eq.Prod]
  else
    repeat rw [Softmax.eq.One.of.LeLength (by omega)]


-- created on 2025-12-04
