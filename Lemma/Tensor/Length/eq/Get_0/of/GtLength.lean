import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[main]
private lemma main
-- given
  (h : s.length > n)
  (t : Tensor α s) :
-- imply
  t.length = s[0] := by
-- proof
  apply Length.eq.Get_0.of.GtLength_0


-- created on 2025-06-25
