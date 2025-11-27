import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.List.EqPermute__0
import Lemma.List.EqRotate_Length
import Lemma.List.EqTake.of.LeLength
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Rotate_SubLength_1.of.GtLength_0
import Lemma.List.RotateRotate.eq.Rotate_Add
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteHeadCast.eq.Cast_PermuteHead.of.Eq
import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.SEqPermuteHeadPermuteTail.of.Ne_Nil
open Bool List Nat Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨d, by omega⟩ (-d)).permute ⟨0, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := d) (j := 0) ⟨by omega, by omega⟩
  simp at h_permute
  split_ifs with h_d
  ·
    subst h_d
    apply SEqCast.of.SEq.Eq
    ·
      rw [h_permute]
      simp [EqPermute__0]
    ·
      apply SEqPermute__0
  ·
    apply SEqCast.of.SEq.Eq
    ·
      simp [Permute.eq.Append_AppendRotateTakeDrop]
    ·
      subst h
      rw [EqAddSub.of.Ge (by omega)]
      rw [@Tensor.Permute.eq.Ite]
      simp
      split_ifs with h_gt_1
      ·
        omega
      ·
        have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 (s.length - 1)
        rw [EqAdd_Sub.of.Ge (by omega)] at h_toNat
        rw [PermuteHeadCast.eq.Cast_PermuteHead.of.Eq]
        ·
          apply SEqCast.of.SEq.Eq
          ·
            rw [h_toNat]
            simp
            repeat rw [Drop.eq.Nil.of.LeLength (by simp)]
            simp
            repeat rw [EqTake.of.LeLength (by simp)]
            rw [Permute__Neg.eq.Rotate_SubLength_1.of.GtLength_0]
            omega
          ·
            rw [h_toNat]
            apply SEqPermuteHeadPermuteTail.of.Ne_Nil
            aesop
        ·
          rw [h_toNat]
          simp
          rw [Permute__Neg.eq.Rotate_SubLength_1.of.GtLength_0]
          omega


-- created on 2025-10-26
