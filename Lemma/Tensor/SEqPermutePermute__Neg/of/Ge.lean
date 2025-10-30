import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Tensor.SEqPermutePermute__Neg.of.GtLength_Add
open Tensor Nat


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).permute ⟨i - d, by simp; omega⟩ d ≃ X := by
-- proof
  have := SEqPermutePermute__Neg.of.GtLength_Add (i := i - d) (d := d) (by omega) X
  apply SEq.symm ∘ SEq.trans this.symm
  repeat apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ (by omega) rfl
  rfl


-- created on 2025-10-30
