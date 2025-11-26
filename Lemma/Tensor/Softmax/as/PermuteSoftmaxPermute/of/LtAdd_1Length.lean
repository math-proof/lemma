import Lemma.Tensor.SEqSoftmaxS.of.SEq.Eq
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SoftmaxPermute.as.PermuteSoftmax.of.GtLength_Add
open Tensor


@[main]
private lemma main
  [ExpPos α]
-- given
  (h : i + 1 < s.length)
  (X : Tensor α s) :
-- imply
  let d := s.length - 1 - i
  X.softmax i ≃ (X.permute ⟨i, by omega⟩ d).softmax.permute ⟨s.length - 1, by simp; omega⟩ (-d) := by
-- proof
  intro d
  have := SoftmaxPermute.as.PermuteSoftmax.of.GtLength_Add (i := i) (d := d) (by omega) X
  have h_id : i + d = s.length - 1 := by omega
  have := Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength (i := i + d) (i' := i + d) (d := -d) (d' := -d) (by simp; omega) (by omega) (by omega) this
  simp [h_id] at this
  have h_sim: ((X.permute ⟨i, by omega⟩ d).softmax (s.length - 1)).permute ⟨i + d, by simp; grind⟩ (-d) ≃ (X.permute ⟨i, by omega⟩ d).softmax.permute ⟨s.length - 1, by simp; grind⟩ (-d) := by
    apply Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
    .
      omega
    .
      rfl
    .
      apply Tensor.SEqSoftmaxS.of.SEq.Eq
      .
        simp
      .
        rfl
  have := this.trans h_sim
  apply SEq.symm ∘ SEq.trans this.symm
  apply Tensor.SEqPermutePermute.of.GtLength_Add (i := i) (d := d) (by omega) (X.softmax i)


-- created on 2025-10-12
-- updated on 2025-10-31
