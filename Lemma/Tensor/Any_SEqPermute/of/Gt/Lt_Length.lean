import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.SEqPermutePermute.of.Gt.Lt_Length
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
  ∃ Y : Tensor α (s.permute ⟨i, by grind⟩ (-d)), Y.permute ⟨j, by simp [LengthPermute.eq.Length]; omega⟩ d ≃ X := by
-- proof
  intro d
  use X.permute ⟨i, by linarith⟩ (-d)
  apply SEqPermutePermute.of.Gt.Lt_Length h_i h


-- created on 2025-10-25
