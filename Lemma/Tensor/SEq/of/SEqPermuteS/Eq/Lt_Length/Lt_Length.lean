import Lemma.Tensor.SEqPermutePermute__Neg.of.Ge
import Lemma.Int.EqNegToNatNeg.of.Lt_0
import Lemma.Tensor.SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
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
  have h_length := EqLengthS.of.SEq.shape h
  by_cases h_d : d ≥ 0
  .
    simp at h_length
    have h_toNat := Int.EqToNat.of.Ge_0 h_d
    by_cases h_d : i + d.toNat < s.length
    .
      have h := h_toNat.symm ▸ h
      apply Tensor.SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add h_d h_i h_i' h_eq h
    .
      simp at h_d
      have h_A := Tensor.SEqPermuteS.of.Add.ge.SubLength_1 (i := ⟨i, by grind⟩) (d := d.toNat) (by simp; omega) A
      rw [h_toNat] at h_A
      have h := h.symm.trans h_A
      have h_B := Tensor.SEqPermuteS.of.Add.ge.SubLength_1 (i := ⟨i, by grind⟩) (d := d.toNat) (by simp; omega) B
      rw [h_toNat] at h_B
      have := Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length (dim := i) (dim' := i') (k' := d) (k := d) (A := B) (B := B) (by omega) (by omega) (by rfl) (by rfl)
      have h_B := this.trans h_B
      have h := h.symm.trans h_B
      simp at h
      apply Tensor.SEq.of.SEqPermuteS.Eq.Lt_Length.Lt_Length.GtLength_Add (d := s.length - 1 - i) _ h_i h_i' h_eq
      .
        have := Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length (dim := i') (dim' := i) (k' := (s'.length - 1 - i : ℕ)) (k := (s.length - 1 - i : ℕ)) (A := B) (B := B) (by omega) (by omega) (by simp; grind) (by rfl)
        have h := h.trans this
        apply SEq.symm ∘ SEq.trans h.symm
        rfl
      .
        omega
  .
    have h_neg : d < 0 := by omega
    by_cases h_d : i ≥ (-d).toNat
    .
      have h_toNat := Int.EqNegToNatNeg.of.Lt_0 h_neg
      have h : (A.permute ⟨i, h_i⟩ (-↑(-d).toNat)).permute ⟨i - (-d).toNat, by simp; omega⟩ (-d).toNat ≃ (B.permute ⟨i', h_i'⟩ (-↑(-d).toNat)).permute ⟨i' - (-d).toNat, by simp [← h_eq]; omega⟩ (-d).toNat := by
        apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ (by omega) rfl
        rw [h_toNat]
        exact h.symm
      have h_A := SEqPermutePermute__Neg.of.Ge (i := ⟨i, by grind⟩) h_d A
      simp at h_A
      have h := h.symm.trans h_A
      have h_B := SEqPermutePermute__Neg.of.Ge (i := ⟨i', by grind⟩) (h_eq ▸ h_d) B
      simp at h_B
      exact h.symm.trans h_B
    .
      simp at h_d
      sorry


-- created on 2025-10-25
