import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqPermute__0
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Add
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
open Bool List Nat Tensor


@[main]
private lemma main
  [Add α] [Zero α]
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
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    rw [Add.comm] at h_toNat
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
    unfold permuteTail Tensor.rotate
    simp
    sorry


-- created on 2025-10-31
-- updated on 2025-11-06
