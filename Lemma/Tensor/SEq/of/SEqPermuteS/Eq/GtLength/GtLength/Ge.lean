import Lemma.Tensor.SEqPermutePermute__Neg.of.Ge
import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_d : i ≥ d)
  (h_i : s.length > i)
  (h_i' : i' < s'.length)
  (h_eq : i = i')
  (h : A.permute ⟨i, h_i⟩ (-d) ≃ B.permute ⟨i', h_i'⟩ (-d)) :
-- imply
  A ≃ B := by
-- proof
  have h : (A.permute ⟨i, h_i⟩ (-d)).permute ⟨i - d, by simp; omega⟩ d ≃ (B.permute ⟨i', h_i'⟩ (-d)).permute ⟨i' - d, by simp [← h_eq]; omega⟩ d := by
    apply SEqPermuteS.of.SEq.Eq.Eq.GtLength _ (by omega) rfl
    exact h.symm
  have h_A := SEqPermutePermute__Neg.of.Ge (i := ⟨i, by grind⟩) h_d A
  simp at h_A
  have h := h.symm.trans h_A
  have h_B := SEqPermutePermute__Neg.of.Ge (i := ⟨i', by grind⟩) (h_eq ▸ h_d) B
  simp at h_B
  exact h.symm.trans h_B


-- created on 2025-10-31
