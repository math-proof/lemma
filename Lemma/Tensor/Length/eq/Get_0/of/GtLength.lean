import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[path]
private lemma main
-- given
  (h : s.length > n)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  apply Length.eq.Get_0.of.GtLength_0


-- created on 2025-06-25
