import Lemma.Int.EqToNat.of.Gt_0
import Lemma.Int.ToNatNeg.eq.Neg.of.Lt_0
import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.Add.ge.SubLength_1
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SEqPermute__0
open Tensor Int


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_d : s.length > i + d)
  (h_i : i < s.length)
  (h_i' : i' < s'.length)
  (h_eq : i = i')
  (h : A.permute ⟨i, h_i⟩ d ≃ B.permute ⟨i', h_i'⟩ d) :
-- imply
  A ≃ B := by
-- proof
  have h_length := Length.of.SEq.shape h
  simp at h_length
  have h : (A.permute ⟨i, h_i⟩ d).permute ⟨i + d, by simp; omega⟩ (-d) ≃ (B.permute ⟨i', h_i'⟩ d).permute ⟨i' + d, by simp [← h_eq]; omega⟩ (-d) := by
    apply SEqPermuteS.of.SEq.Eq.Eq.GtLength _ _ rfl h.symm
    simp [← h_eq]
  have h_A := SEqPermutePermute.of.GtLength_Add h_d A (d := d)
  have : (A.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp; omega⟩ (-d) ≃ (A.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp; omega⟩ (-d) := by
    apply SEqPermuteS.of.SEq.Eq.Eq.GtLength _ (by rfl)
    omega
    rfl
  have h_A := h_A.symm.trans this
  have h_B := SEqPermutePermute.of.GtLength_Add (show i' + d < s'.length by omega) B
  have : (B.permute ⟨i', by omega⟩ d).permute ⟨i' + d, by simp; omega⟩ (-d) ≃ (B.permute ⟨i', by omega⟩ d).permute ⟨i' + d, by simp; omega⟩ (-d) := by
    apply SEqPermuteS.of.SEq.Eq.Eq.GtLength _ (by rfl)
    omega
    rfl
  have h_B := h_B.symm.trans this
  exact (h_A.trans h).trans h_B.symm


-- created on 2025-10-30
