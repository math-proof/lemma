import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Nat.OfNat.eq.Cast
import Lemma.List.Permute.eq.Rotate.of.GtLength_0
import Lemma.List.EqRotatePermute.of.GtLength_0
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Nat.ToNatAdd.eq.Add
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Tensor.PermuteTailCast.eq.Cast_PermuteTail.of.Eq
import Lemma.Tensor.SEqPermuteTailPermuteHead
open Bool List Tensor Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨0, by omega⟩ d).permute ⟨d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d
  rw [Permute.eq.Ite (d := ⟨d, by simp [LengthPermute.eq.Length]; omega⟩) (k := -d)]
  simp
  split_ifs with h_sub h_neg h'
  repeat omega
  ·
    have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := 0) (j := s.length - 1) ⟨by omega, by omega⟩
    simp at h_permute
    apply SEqCast.of.SEq.Eq.Eq
    ·
      simp [LengthPermute.eq.Length]
      have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatAdd.eq.Add 1 d
      rw [h_toNat]
      subst h
      rw [EqAdd_Sub.of.Ge (by omega)]
      simp
      rw [h_permute]
      apply EqRotatePermute.of.GtLength_0
    ·
      subst h
      rw [h_permute]
    ·
      have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
      rw [h_toNat]
      subst h
      rw [EqAdd_Sub.of.Ge (by omega)]
      rw [@Tensor.Permute.eq.Ite]
      simp
      split_ifs with h_gt_1 h_eq_0
      ·
        have h_cancel := EqAddSub.of.Ge (a := 1) (b := s.length) (by omega)
        rw [PermuteTailCast.eq.Cast_PermuteTail.of.Eq]
        ·
          apply SEqCast.of.SEq.Eq.Eq
          ·
            simp [LengthPermute.eq.Length]
            simp [h_cancel]
            simp [Permute.eq.Rotate.of.GtLength_0]
          ·
            simp [LengthPermute.eq.Length]
            apply Eq_RotatePermute.of.GtLength_0
          ·
            rw [h_cancel]
            apply SEqPermuteTailPermuteHead
        ·
          simp [h_cancel]
          simp [Permute.eq.Rotate.of.GtLength_0]
      ·
        omega
      ·
        omega
  ·
    simp [LengthPermute.eq.Length] at h'
    contradiction


-- created on 2025-10-19
-- updated on 2025-10-20
