import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.Eq.Lt_Length
import Lemma.Algebra.Lt_Sub.of.LtAdd
open Tensor Algebra


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim + 1 < s.length)
  (X : Tensor α s) :
-- imply
  have h_length : s.length > 0 := by linarith
  have := Length.eq.Get_0.of.GtLength_0 h_length X
  X.sum (dim + 1) ≃ [i < s[0]] (X[i].sum dim) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Sum.as.Stack_Sum.of.Eq.Lt_Length rfl
    apply Lt_Sub.of.LtAdd.nat h


-- created on 2025-06-27
-- updated on 2025-07-13
