import Lemma.List.TakeDropPermute.eq.TakeDrop.of.GtLength_Add
import Lemma.List.TakeDropTake.eq.TakeDrop
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s.length > i + d) :
-- imply
  (((s.permute i d).take (i + d + 1)).drop i).take d = (s.drop (i + 1)).take d := by
-- proof
  rw [TakeDropTake.eq.TakeDrop]
  apply TakeDropPermute.eq.TakeDrop.of.GtLength_Add h


-- created on 2025-10-25
