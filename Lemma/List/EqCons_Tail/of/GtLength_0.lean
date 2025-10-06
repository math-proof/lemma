import Lemma.List.EqCons_Tail.of.NeLength_0
import Lemma.Algebra.Ne.of.Gt
open Algebra List


@[main, comm]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v[0] :: v.tail = v := by
-- proof
  have h := Ne.of.Gt h
  apply EqCons_Tail.of.NeLength_0 h


-- created on 2025-06-09
-- updated on 2025-06-15
