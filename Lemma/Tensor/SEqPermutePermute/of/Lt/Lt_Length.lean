import Lemma.Nat.Add
import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
open Nat Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_j : j < s.length)
  (h : i < j)
  (X : Tensor α s) :
-- imply
  let d := j - i
  (X.permute ⟨i, by linarith⟩ d).permute ⟨j, by simpa⟩ (-d) ≃ X := by
-- proof
  intro d
  have : NeZero d := ⟨by omega⟩
  have := SEqPermutePermute.of.GtLength_Add (s := s) (i := i) (d := d) (by grind) X
  simp [d] at this ⊢
  apply SEq.symm ∘ SEq.trans this.symm
  apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ (by rfl) (by rfl)
  apply EqAdd_Sub.of.Ge
  omega


-- created on 2025-10-12
-- updated on 2025-10-22
