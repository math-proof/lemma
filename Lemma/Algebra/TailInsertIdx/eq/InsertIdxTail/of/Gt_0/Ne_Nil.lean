import Lemma.Algebra.TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil
import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


@[main]
private lemma main
  {v : List α}
-- given
  (h : v ≠ [])
  (h_n : n > 0) :
-- imply
  (v.insertIdx n x).tail = v.tail.insertIdx (n - 1) x := by
-- proof
  have := TailInsertIdx.eq.InsertIdxTail.of.Ne_Nil h (n - 1) x
  rw [EqAddSub.of.Ge (by linarith)] at this
  assumption


-- created on 2025-07-13
