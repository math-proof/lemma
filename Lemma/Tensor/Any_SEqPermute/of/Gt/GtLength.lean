import Lemma.Tensor.SEqPermutePermute.of.Gt.GtLength
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_i : i < s.length)
  (h : i > j)
  (X : Tensor α s) :
-- imply
  let d := i - j
  ∃ Y : Tensor α (s.permute ⟨i, by grind⟩ (-d)), Y.permute ⟨j, by simp; omega⟩ d ≃ X := by
-- proof
  intro d
  use X.permute ⟨i, by linarith⟩ (-d)
  apply SEqPermutePermute.of.Gt.GtLength h_i h


-- created on 2025-10-25
