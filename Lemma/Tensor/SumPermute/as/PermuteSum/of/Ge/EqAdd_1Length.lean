import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.Append_TakeDrop.eq.Take.of.Ge
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.GetRotate.eq.Ite.of.Le_Length.Lt_Length
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.LtSub.of.Lt
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataSelect.eq.Cast_SelectSplitAtData.of.GtLength_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
open List Bool Int Nat Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  [NeZero (d : ℕ)]
  {i : Fin s.length}
-- given
  (h_i : i.val + 1 = s.length)
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  simp [@Tensor.Permute.eq.Ite]
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  rw [Add.comm] at h_toNat
  have h_sub_lt : (s.permute i (-d)).length > i - d := by 
    simp
    apply LtSub.of.Lt i.isLt
  have := NeZero.pos d
  split_ifs with h_d0 h_pos? h_i0 h_i
  repeat omega
  rw [SumCast.eq.Cast_Sum.of.Eq]
  ·
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [h_toNat]
      rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
    ·
      rw [EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h_d]
    ·
      rw [h_toNat]
      unfold permuteTail Tensor.rotate
      simp
      rw [Sum.eq.Sum_Select]
      rw [Sum.eq.Sum_Select.of.GtLength (by simp; omega)]
      have h_eraseIdx : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).eraseIdx (↑i - d) = s.eraseIdx ↑i := by 
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simp; omega)]
        simp
        rw [EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add (by simp; omega)]
        conv_rhs => rw [EraseIdx.eq.Append_Drop_Add_1]
        rw [EqMin.of.Le (by omega)]
        simp [h_i]
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)]
        rw [Add.comm (a := 1)]
        simp
        rw [AddAdd.eq.Add_Add]
        rw [EqAddSub.of.Ge (by omega)]
        simp
        rw [EqAddSub.of.Ge (by omega)]
        simp
        have := Append_TakeDrop.eq.Take.of.Ge (s := s) (i := s.length - 1) (d := d) (by omega)
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)] at this
        rwa [Add.comm (a := 1)] at this
      have h_get : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))[↑i - d]'(by simp; omega) = s[i] := by 
        rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp; omega)]
        rw [GetRotate.eq.Ite.of.Le_Length.Lt_Length (by simp; omega) (by simp; omega)]
        simp_all
        split_ifs with h_lt
        ·
          simp [EqMin.of.Le (show (d + 1) ≤ s.length by omega)]
          simp only [GetElem.getElem]
          apply congrArg
          simp
          omega
        ·
          omega
      apply SEqSumS.of.All_SEq.Eq.Eq h_eraseIdx h_get
      ·
        intro t
        have h_t := t.isLt
        apply SEq.of.SEqDataS.Eq h_eraseIdx
        ·
          repeat rw [DataSelect.eq.Cast_SelectSplitAtData.of.GtLength_0]
          simp
          apply SEqCastS.of.SEq.Eq.Eq
          ·
            simp [List.Vector.length]
            have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
            simp_all
          ·
            simp [List.Vector.length]
            rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
            simp_all
          ·
            sorry
  ·
    rw [h_toNat]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
  ·
    omega


-- created on 2025-11-16
