import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.SubAddS.eq.Sub
import Lemma.List.LengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.List.EqPermute__0
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.Get.dvd.ProdTake.of.Lt_Length
import Lemma.List.GetPermute__Neg.eq.Get.of.Ge.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.Nat.Add
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.LtVal
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataSelect.eq.Cast_SelectSplitAtData.of.GtLength_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Vector Bool Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
  [AddCommMonoid α]
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  rw [@Tensor.Permute.eq.Ite]
  simp
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  rw [Add.comm] at h_toNat
  split_ifs with h_d0 h_pos? h_i0 h_i
  ·
    subst h_d0
    simp
    apply SumCast.as.Sum.of.Eq
    rw [EqPermute__0]
  ·
    omega
  ·
    omega
  ·
    rw [SumCast.eq.Cast_Sum.of.Eq]
    ·
      apply SEqCast.of.SEq.Eq.Eq
      ·
        rw [h_toNat]
        rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
      ·
        rw [EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h]
      ·
        rw [h_toNat]
        unfold permuteTail Tensor.rotate
        simp
        sorry
    ·
      rw [h_toNat]
      rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
  ·
    rw [Sum.eq.Sum_Select]
    rw [Sum.eq.Sum_Select.of.GtLength]
    have h_eraseIdx := EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h
    have h_get := GetPermute__Neg.eq.Get.of.Ge.GtLength (d := d) i.isLt h
    apply SEqSumS.of.All_SEq.Eq.Eq h_eraseIdx h_get
    ·
      intro t
      have h_t := LtVal t
      apply SEq.of.SEqDataS.Eq h_eraseIdx
      ·
        simp
        repeat rw [DataSelect.eq.Cast_SelectSplitAtData.of.GtLength_0]
        simp
        simp [h_get] at h_t
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
          rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
          simpa [h_get]
        ·
          simp
          rw [List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength (by omega) (by omega)]
          rw [ProdEraseIdx.eq.MulProdS]
        ·
          simp at h_get
          apply SEq.of.All_EqGetS.Eq.fin
          ·
            intro k
            have h_k := LtVal k
            obtain ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_k
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
            ·
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [GetCast.eq.Get.of.Eq.fin]
              .
                -- rw [h_toNat]
                -- unfold permuteTail Tensor.rotate
                sorry
              .
                rw [h_toNat]
                rw [MulProdS.eq.ProdAppend]
                apply congrArg
                simp
                rw [EqMin.of.Le (by apply LeAdd_1)]
                rw [SubAddS.eq.Sub]
                rw [EqMin.of.Le (LeAddS.of.Le 1 h)]
                rw [EqSubAdd]
                rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
                rw [EqMin.of.Le (by omega)]
                rw [Append_Append.eq.AppendAppend]
            ·
              apply Get.dvd.ProdTake.of.Lt_Length
            ·
              have h_q := LtVal q
              simp [List.Vector.length] at h_q
              have h_sub_lt: (s.permute i (-↑d)).length > ↑i - d := by
                simp
                apply LtSub.of.Lt i.isLt
              rw [List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength h_sub_lt (by simpa [h_get])] at h_q
              simp [ProdTake.eq.MulProdTake.of.Lt_Length h_sub_lt]
              rwa [EqDivMul.of.Ne_0]
              rw [h_get]
              apply Nat.Ne_0.of.Gt h_t
            ·
              simpa [h_get]
          ·
            simp
            rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
            ·
              rw [List.LengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength _ h_t]
              rw [h_eraseIdx]
            ·
              simpa [h_get]
      ·
        simp
        omega


-- created on 2025-10-31
-- updated on 2025-11-15
