import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s ≠ [])
  (h_n : n > 0) :
-- imply
  (s.insertIdx n x).tail = s.tail.insertIdx (n - 1) x := by
-- proof
  have := TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil h (n - 1) x
  rwa [EqAddSub.of.Ge (by linarith)] at this


-- created on 2025-07-13
