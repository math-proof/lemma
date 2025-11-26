import Lemma.Tensor.SEqPermutePermute.of.GtLength_Add
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
open Tensor


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i - d, by omega⟩ d).permute ⟨i, by simp⟩ (-d) ≃ X := by
-- proof
  have := SEqPermutePermute.of.GtLength_Add (i := i - d) (d := d) (by omega) X
  apply SEq.symm ∘ SEq.trans this.symm
  repeat apply SEqPermuteS.of.SEq.Eq.Eq.GtLength _ (by omega) rfl
  rfl


-- created on 2025-10-30
