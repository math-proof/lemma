import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open List Tensor


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > 0) :
-- imply
  X.length = s.headD 1 := by
-- proof
  have h := GtLength_0.of.GtLength_0 h
  have h := Length.eq.Get_0.of.GtLength_0 h X
  rwa [HeadD.eq.Get_0.of.GtLength_0]


-- created on 2025-10-12
