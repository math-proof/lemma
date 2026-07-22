import Lemma.Tensor.SEqSum.of.LeLength
open Tensor


@[main, cast]
private lemma main
  [AddZeroClass α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.sum d ≃ X := by
-- proof
  apply SEqSum.of.LeLength h


-- created on 2025-11-28
