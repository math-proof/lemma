import Lemma.Tensor.SEqPermutePermute__Neg.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
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
  (X.permute ⟨i, by linarith⟩ (-d)).permute ⟨j, by simp; omega⟩ d ≃ X := by
-- proof
  intro d
  have : NeZero d := ⟨by omega⟩
  have := SEqPermutePermute__Neg.of.GtLength_Add (s := s) (i := j) (d := d) (by omega) X
  simp [d] at this ⊢
  apply SEq.symm ∘ SEq.trans this.symm
  apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ rfl rfl
  apply Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ rfl
  .
    rfl
  .
    grind


-- created on 2025-10-25
-- updated on 2025-10-26
