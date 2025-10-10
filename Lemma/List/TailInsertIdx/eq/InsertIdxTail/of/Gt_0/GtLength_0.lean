import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.Gt_0.Ne_Nil
import Lemma.List.Ne_Nil.is.GtLength_0
open List


@[main, comm]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0)
  (h_n : n > 0)
  (x : α) :
-- imply
  (v.insertIdx n x).tail = v.tail.insertIdx (n - 1) x := by
-- proof
  have h := Ne_Nil.of.GtLength_0 h
  apply TailInsertIdx.eq.InsertIdxTail.of.Gt_0.Ne_Nil h h_n


-- created on 2025-07-13
