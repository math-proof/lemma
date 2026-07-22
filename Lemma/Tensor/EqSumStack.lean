import Lemma.Tensor.EqSumUnsqueeze
import Lemma.Tensor.Stack.eq.Unsqueeze
open Tensor


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (X : Tensor α s) :
-- imply
  ∑ _ < 1, X = X := by
-- proof
  rw [Stack.eq.Unsqueeze]
  apply EqSumUnsqueeze


-- created on 2026-07-22
