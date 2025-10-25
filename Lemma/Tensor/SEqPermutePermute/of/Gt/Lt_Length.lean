import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermutePermute.of.Lt.Lt_Length
open List Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_i : i < s.length)
  (h : i > j)
  (X : Tensor α s) :
-- imply
  let d := i - j
  have h_length_permute := LengthPermute.eq.Length s (i := ⟨i, by grind⟩) (d := -d)
  (X.permute ⟨i, by linarith⟩ (-d)).permute ⟨j, by simp [h_length_permute]; omega⟩ d ≃ X := by
-- proof
  intro d h_length_permute
  have : NeZero d := ⟨by omega⟩
  have := SEqPermutePermute.of.Lt.Lt_Length (i := j) (j := i) (by simp [h_length_permute]; omega) h (X.permute ⟨i, by linarith⟩ (-d))
  simp at this
  subst d
  have := Tensor.SEqPermuteS.of.SEq.Lt_Length (dim := j) (by simp [LengthPermute.eq.Length]; omega) this (i - j : ℕ)
  sorry


-- created on 2025-10-25
