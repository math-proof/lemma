import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil
import Lemma.List.Ne_Nil.is.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (n : ℕ)
  (x : α) :
-- imply
  (s.insertIdx (n + 1) x).tail = s.tail.insertIdx n x := by
-- proof
  apply TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil ∘ Ne_Nil.of.GtLength_0
  assumption


-- created on 2025-10-10
