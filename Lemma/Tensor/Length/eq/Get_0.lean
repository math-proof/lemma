import Lemma.Nat.Gt_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Nat Tensor List


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (i : Fin X.length) :
-- imply
  X.length = s[0]'(GtLength_0.of.GtLength_0 (Gt_0 i)) :=
-- proof
  Length.eq.Get_0.of.GtLength_0 _ X


-- created on 2026-07-12
