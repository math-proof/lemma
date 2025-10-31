import Lemma.Int.EqNegToNatNeg.of.Lt_0
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Tensor.EqLengthS.of.SEq
import Lemma.Tensor.SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.Ge
import Lemma.Tensor.SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.Add.ge.SubLength_1
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
import Lemma.Tensor.SEqPermuteS__Neg.of.Le
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
  have h_length := EqLengthS.of.SEq.shape h
  by_cases h_d : d ≥ 0
  ·
    simp at h_length
    have h_toNat := EqToNat.of.Ge_0 h_d
    by_cases h_d : i + d.toNat < s.length
    ·
      have h := h_toNat.symm ▸ h
      apply SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add h_d h_i h_i' h_eq h
    ·
      simp at h_d
      have h_A := SEqPermuteS.of.Add.ge.SubLength_1 (i := ⟨i, by grind⟩) (d := d.toNat) (by simp; omega) A
      rw [h_toNat] at h_A
      have h := h.symm.trans h_A
      have h_B := SEqPermuteS.of.Add.ge.SubLength_1 (i := ⟨i, by grind⟩) (d := d.toNat) (by simp; omega) B
      rw [h_toNat] at h_B
      have := SEqPermuteS.of.SEq.Eq.Eq.Lt_Length (i := i) (i' := i') (d := d) (d' := d) (A := B) (B := B) (by omega) (by omega) (by rfl) (by rfl)
      have h_B := this.trans h_B
      have h := h.symm.trans h_B
      simp at h
      apply SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add (d := s.length - 1 - i) _ h_i h_i' h_eq
      ·
        have := SEqPermuteS.of.SEq.Eq.Eq.Lt_Length (i := i') (i' := i) (d := (s.length - 1 - i : ℕ)) (d' := (s'.length - 1 - i : ℕ)) (A := B) (B := B) (by omega) (by omega) (by simp; grind) (by rfl)
        have h := h.trans this
        apply SEq.symm ∘ SEq.trans h.symm
        rfl
      ·
        omega
  ·
    have h_neg : d < 0 := by omega
    have h_toNat := EqNegToNatNeg.of.Lt_0 h_neg
    by_cases h_d : i ≥ (-d).toNat
    ·
      apply SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.Ge h_d h_i h_i' h_eq
      rwa [h_toNat]
    ·
      simp at h_d
      have := SEqPermuteS__Neg.of.Le (i := ⟨i, by grind⟩) (d := (-d).toNat) (by simp; omega) A
      rw [h_toNat] at this
      simp at this
      have h := h.symm.trans this
      have := SEqPermuteS__Neg.of.Le (i := ⟨i', by grind⟩) (d := (-d).toNat) (by simp; omega) B
      rw [h_toNat] at this
      simp at this
      have h := h.symm.trans this
      apply SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.Ge (d := i) _ (by omega) (by omega) h_eq
      ·
        have := SEqPermuteS.of.SEq.Eq.Eq.Lt_Length (i := i') (i' := i') (d' := -i') (d := -i) (A := B) (B := B) (by omega) (by omega) (by simp; omega) (by rfl)
        exact h.trans this
      ·
        simp


-- created on 2025-10-25
-- updated on 2025-10-31
