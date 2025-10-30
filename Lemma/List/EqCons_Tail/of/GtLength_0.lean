import Lemma.List.EqCons_Tail.of.NeLength_0
import Lemma.Nat.Ne.of.Gt
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s[0] :: s.tail = s := by
-- proof
  have h := Ne.of.Gt h
  apply EqCons_Tail.of.NeLength_0 h


-- created on 2025-06-09
-- updated on 2025-06-15
