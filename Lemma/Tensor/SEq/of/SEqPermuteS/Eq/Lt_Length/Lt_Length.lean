import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
import Lemma.Tensor.EqLengthS.of.SEq
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Int.EqToNat.of.Gt_0
import Lemma.Int.ToNatNeg.eq.Neg.of.Lt_0
open Tensor Int


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i < s.length)
  (h_i' : i' < s'.length)
  (h_eq : i = i')
  (h : A.permute ⟨i, h_i⟩ d ≃ B.permute ⟨i', h_i'⟩ d) :
-- imply
  A ≃ B := by
-- proof
  by_cases h_d : d = 0
  .
    subst h_d
    have h_A := SEqPermute__0 A ⟨i, by omega⟩
    have h_B := SEqPermute__0 B ⟨i', by omega⟩
    apply (h_A.symm.trans h).trans h_B
  .
    have h_length := EqLengthS.of.SEq.shape h
    by_cases h_pos : d > 0
    .
      simp at h_length
      by_cases h_d : i + d.toNat < s.length
      .
        have h : (A.permute ⟨i, h_i⟩ d).permute ⟨i + d.toNat, by simp; omega⟩ (-d) ≃ (B.permute ⟨i', h_i'⟩ d).permute ⟨i' + d.toNat, by simp [← h_eq]; omega⟩ (-d) := by
          apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ rfl h.symm
          simp [← h_eq]
        have : NeZero d.toNat := ⟨by omega⟩
        have h_toNat := Int.EqToNat.of.Gt_0 h_pos
        have h_A := SEqPermutePermute.of.GtLength_Add h_d A
        have : (A.permute ⟨i, by omega⟩ d.toNat).permute ⟨i + d.toNat, by simp; omega⟩ (-d.toNat) ≃ (A.permute ⟨i, by omega⟩ d).permute ⟨i + d.toNat, by simp; omega⟩ (-d) := by
          apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ (by rfl)
          repeat rw [h_toNat]
        have h_A := h_A.symm.trans this
        have h_B := SEqPermutePermute.of.GtLength_Add (show i' + d.toNat < s'.length by omega) B
        have : (B.permute ⟨i', by omega⟩ d.toNat).permute ⟨i' + d.toNat, by simp; omega⟩ (-d.toNat) ≃ (B.permute ⟨i', by omega⟩ d).permute ⟨i' + d.toNat, by simp; omega⟩ (-d) := by
          apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ (by rfl)
          repeat rw [h_toNat]
        have h_B := h_B.symm.trans this
        exact (h_A.trans h).trans h_B.symm
      .
        sorry
    .
      have h_neg : d < 0 := by omega
      by_cases h_d : i ≥ (-d).toNat
      .
        have h : (A.permute ⟨i, h_i⟩ d).permute ⟨i - (-d).toNat, by simp; omega⟩ (-d) ≃ (B.permute ⟨i', h_i'⟩ d).permute ⟨i' - (-d).toNat, by simp [← h_eq]; omega⟩ (-d) := by
          apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ rfl h.symm
          simp [← h_eq]
        have h_toNat := ToNatNeg.eq.Neg.of.Lt_0 h_neg
        sorry
      .
        sorry


-- created on 2025-10-25
