import Lemma.List.Ne_Nil.is.GtLength_0
open List


@[main, comm, mp, mpr]
private lemma main
-- given
  (s : List α) :
-- imply
  s ≠ [] ↔ s.length ≥ 1 := by
-- proof
  rw [Ne_Nil.is.GtLength_0]
  aesop


-- created on 2025-10-20
