import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Sum.ne.Zero.of.All_Gt_0.Ne_0
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeInsertIdxEraseIdx.eq.Take
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.NotGt.is.Le
import Lemma.Real.EqLog1'0
import Lemma.Real.GtExp_0
import Lemma.Real.NeExp_0
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.EqLogExp
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Tensor.LogDiv.eq.SubLogS.of.All_Ne_0.All_Ne_0
import Lemma.Tensor.Max.eq.Cast.of.LeLength
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Softmax.eq.One.of.LeLength
import Lemma.Tensor.SoftmaxSub_Keepdim.eq.Softmax
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
open Fin List Nat Real Tensor Vector


/--
自然语言论述：[flash_attn](http://myhz0606.com/article/flash_attn)
-/
@[main]
private lemma main
  [NeZero s.prod]
  [LT α] [DecidableLT α]
  [LogPos α] [IsOrderedCancelAddMonoid α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  log (X.softmax d) = X - (X.max d).keepdim - log ((exp (X - (X.max d).keepdim)).sum d).keepdim := by
-- proof
  if h : s.length > d then
    have := SoftmaxSub_Keepdim.eq.Softmax X (X.max d)
    have := congrArg Log.log this
    rw [Softmax.eq.Div_SumExp] at this
    rw [← this]
    rw [@Tensor.LogDiv.eq.SubLogS.of.All_Ne_0.All_Ne_0]
    ·
      rw [@Tensor.EqLogExp]
    ·
      intro t
      simp [DataExp.eq.ExpData]
      simp only [GetElem.getElem]
      simp [GetExp.eq.ExpGet.fin]
      apply NeExp_0
    ·
      intro t
      have h_t := t.isLt
      rw [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data (d := ⟨d, h⟩)]
      simp only [GetElem.getElem]
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp
        have h_lt : t < (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) := by
          simp [Mul_Mul.eq.MulMul.comm]
          rwa [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength h]
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        have h_q := q.isLt
        simp [TakeInsertIdxEraseIdx.eq.Take] at h_q
        have h_r := r.isLt
        have h_prod_insertIdx := ProdDropInsertIdxEraseIdx.eq.ProdDrop.of.GtLength h
        simp [h_prod_insertIdx] at h_r
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        simp [GetRepeat.eq.Get_Mod.fin]
        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        rw [GetCast.eq.Get.of.Eq.fin]
        ·
          simp [DataSum.eq.Sum_DataSelect (d := ⟨d, h⟩)]
          rw [GetSum.eq.Sum_Get.fin]
          apply Sum.ne.Zero.of.All_Gt_0.Ne_0
          ·
            grind
          ·
            intro i
            rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              have h_length_slice := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp (s := s) h i.isLt
              have h_lt : ↑q * (((s.eraseIdx d).insertIdx d 1).drop d).prod + ↑r % (((s.eraseIdx d).insertIdx d 1).drop d).prod < ((⟨↑↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod) * (s.drop (d + 1)).prod := by
                simp only [h_length_slice]
                simp [h_prod_insertIdx]
                apply AddMul.lt.Mul.of.Lt.Lt h_q
                apply LtMod.of.Ne_0
                grind
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_q' := q'.isLt
              simp only [h_length_slice] at h_q'
              have h_r' := r'.isLt
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ i.isLt]
              ·
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                simp [DataExp.eq.ExpData]
                rw [GetExp.eq.ExpGet.fin]
                apply GtExp_0
              ·
                simp [ProdTake.eq.MulProdTake.of.GtLength h]
              ·
                simp [ProdTake.eq.MulProdTake.of.GtLength h]
                rwa [EqDivMul.of.Ne_0 (by grind)]
            ·
              apply MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength.simp h i.isLt
        ·
          rw [ProdInsertIdx.eq.Prod]
      ·
        simp [Mul_Mul.eq.MulMul.comm]
        rw [MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength h]
  else
    have h := Le.of.NotGt h
    rw [Softmax.eq.One.of.LeLength h]
    rw [EqLog1'0]
    rw [Keepdim.eq.Cast.of.LeLength h]
    simp [Max.eq.Cast.of.LeLength h]
    rw [Keepdim.eq.Cast.of.LeLength h]
    simp [Sum.eq.Cast_Sum.of.LeLength h]
    apply @Tensor.EqLogExp


-- created on 2025-12-03
-- updated on 2025-12-04
