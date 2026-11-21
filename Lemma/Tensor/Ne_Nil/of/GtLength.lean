import Lemma.Tensor.GtLength_0.of.GtLength
open Tensor


@[path]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > i) :
-- imply
  s ≠ [] := by
-- proof
  apply List.length_pos_iff.mp (GtLength_0.of.GtLength h)


-- created on 2025-06-29
-- updated on 2026-11-20
