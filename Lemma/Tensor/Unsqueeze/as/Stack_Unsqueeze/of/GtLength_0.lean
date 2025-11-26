import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Unsqueeze.as.Stack_Unsqueeze.of.GtLength.Eq
open Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  have := Length.eq.Get_0.of.GtLength_0 h_s X
  X.unsqueeze (d + 1) ≃ [i < s[0]] (X[i].unsqueeze d) := by
-- proof
  match s with
  | []  =>
    contradiction
  | s₀ :: s =>
    apply Unsqueeze.as.Stack_Unsqueeze.of.GtLength.Eq rfl


-- created on 2025-07-13
