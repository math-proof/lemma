import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.Eq.GtLength
import Lemma.Nat.Lt_Sub.of.LtAdd
open Tensor Nat


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : d + 1 < s.length)
  (X : Tensor α s) :
-- imply
  have h_length : s.length > 0 := by linarith
  have := Length.eq.Get_0.of.GtLength_0 h_length X
  X.sum (d + 1) ≃ [i < s[0]] (X[i].sum d) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Sum.as.Stack_Sum.of.Eq.GtLength rfl
    apply Lt_Sub.of.LtAdd h


-- created on 2025-06-27
-- updated on 2025-07-13
