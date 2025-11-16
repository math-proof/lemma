import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.GetPermute__Neg.eq.Get.of.Ge.GtLength
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Add
import Lemma.Nat.LtSub.of.Lt
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
open Int List Nat Tensor Bool


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
  have h_eraseIdx := EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h_d
  have h_get := GetPermute__Neg.eq.Get.of.Ge.GtLength (d := d) i.isLt h_d
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
      sorry
  .
    rw [h_toNat]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
  .
    omega


-- created on 2025-11-16
