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


@[main]
private lemma fn
  [AddZeroClass α]
-- given
  (X : Fin 1 → Tensor α s) :
-- imply
  ∑ i < 1, X i = X 0 := by
-- proof
  rw [← main (X 0)]
  congr 1


-- created on 2026-07-22
