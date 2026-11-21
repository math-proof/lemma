import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[path]
private lemma main
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  have := List.length_pos_iff.mpr h
  s[0] = X.length := by
-- proof
  intro h_length
  apply Get_0.eq.Length.of.GtLength_0 h_length


-- created on 2025-06-29
-- updated on 2026-11-20
