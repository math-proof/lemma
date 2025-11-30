import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Softmax.as.Stack_Softmax.of.Eq.GtLength
open Tensor Nat


@[main]
private lemma main
  [Exp α]
  {d : ℕ}
-- given
  (h : d + 1 < s.length)
  (X : Tensor α s) :
-- imply
  have h_length : s.length > 0 := by linarith
  have := Length.eq.Get_0.of.GtLength_0 h_length X
  X.softmax (d + 1) ≃ [i < s[0]] (X[i].softmax d) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Softmax.as.Stack_Softmax.of.Eq.GtLength rfl
    apply Lt_Sub.of.LtAdd h


-- created on 2025-11-30
