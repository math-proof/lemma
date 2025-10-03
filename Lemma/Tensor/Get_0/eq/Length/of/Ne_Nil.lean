import Lemma.List.GtLength_0.of.Ne_Nil
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor List


@[main]
private lemma main
-- given
  (h : s ≠ [])
  (t : Tensor α s) :
-- imply
  have := GtLength_0.of.Ne_Nil h
  s[0] = t.length := by
-- proof
  intro h_length
  apply Get_0.eq.Length.of.GtLength_0 h_length


-- created on 2025-06-29
